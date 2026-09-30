(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.BaseN.Pulse — C-extractable base16/base64 layer via Pulse + Custard.

Non-recursive leaf encoders/decoders operating on
[Pulse.Lib.Array.array].  Each encode/decode function has a byte-level
post-condition expressed as Pulse separation logic, tying the write to the
pure spec in [Data.BaseN.Base16] / [Data.BaseN.Base64].

Built on the proven pure [Data.BaseN.Base16] and [Data.BaseN.Base64] as spec.
Base08 and Base32 are intentionally excluded — they share the same
arithmetic-bridging pattern and would be mechanical additions.

Written for F* v2026.09.20 (Custard `--custard_backend C`).  Zero admits.

@header Data.BaseN.Pulse

@section Encode
- [encode_base16] — single byte → 2 hex chars into buffer
- [encode_base64_triple] — 3 bytes → 4 base64 chars into buffer
- [encode_base64_tail1] — 1 byte + "==" padding → 4 chars into buffer
- [encode_base64_tail2] — 2 bytes + "=" padding → 4 chars into buffer

@section Decode
- [decode_base16] — 2 hex chars → single byte from buffer
- [decode_base64_quad] — 4 base64 chars → 1-3 bytes from buffer

@section Lemmas
- [lemma_hex_digit_eq_nibble] — bridges [hex_digit] to [nibble_to_upper_hex]
- [lemma_b64_val_i_eq_b64_val] — bridges [b64_val_i] to pure [b64_val]
- [lemma_pulse_base16_roundtrip] — base16 buffer roundtrip
- [lemma_pulse_base64_triple_roundtrip] — base64 3-byte buffer roundtrip
- [lemma_pulse_base64_tail1_roundtrip] — base64 1-byte buffer roundtrip
- [lemma_pulse_base64_tail2_roundtrip] — base64 2-byte buffer roundtrip
*)
module Data.BaseN.Pulse
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
module Cast = FStar.Int.Cast

open FStar.Seq
open FStar.Int.Cast

open Data.BaseN.Base16
open Data.BaseN.Base64

module B16 = Data.BaseN.Base16
module B64 = Data.BaseN.Base64

(* ── Result types (carried over from the old Low* leaf) ─────────────── *)

(** Optional U32 value in [0, 64) — the range of a base64 6-bit value. *)
type opt_u32 =
  | OU_None
  | OU_Some of (v: U32.t{U32.v v < 64})

(** Optional nibble (0..15) — the base16 `unhex` result. *)
type opt_nibble =
  | ON_None
  | ON_Some of (v: U32.t{U32.v v < 16})

(** Optional (byte, bytes-written) pair — the base16 decode result. *)
type opt_result_u8 =
  | OR8_None
  | OR8_Some of (U8.t & U32.t)

(** Optional (bytes, bytes-written) pair — the base64 decode result. *)
type bytes3 = { n: U32.t; b0: U8.t; b1: U8.t; b2: U8.t }

type opt_result_bytes =
  | ORB_None
  | ORB_Some of bytes3

(* ── Pure helpers (erased: noextract so Custard skips them) ─────────── *)

(** Local [pad_byte] to avoid coupling to the [open]-shadowed
    [Data.BaseN.Base64.pad_byte] / [Data.BaseN.Base32.pad_byte]. *)
let pad_byte : U8.t = U8.uint_to_t 0x3D

(** [hex_digit n] converts 0..15 to ASCII hex char (0-9, A-F). *)
let hex_digit (n: U32.t{U32.v n < 16}) : Tot U8.t =
  if U32.lt n 10ul then uint32_to_uint8 (U32.add 48ul n)
  else uint32_to_uint8 (U32.add 55ul n)

(** [unhex c] converts an ASCII hex char to its 0..15 value. *)
let unhex (c: U8.t) : Tot opt_nibble =
  let c32 = uint8_to_uint32 c in
  if U32.lte 48ul c32 && U32.lte c32 57ul then ON_Some (U32.sub c32 48ul)
  else if U32.lte 65ul c32 && U32.lte c32 70ul then ON_Some (U32.sub c32 55ul)
  else if U32.lte 97ul c32 && U32.lte c32 102ul then ON_Some (U32.sub c32 87ul)
  else ON_None

(** [b64_val_i i] converts 0..63 to base64 char. *)
let b64_val_i (i: U32.t{U32.v i < 64}) : Tot U8.t =
  if U32.lte i 25ul then uint32_to_uint8 (U32.add 0x41ul i)
  else if U32.lte i 51ul then uint32_to_uint8 (U32.add 0x61ul (U32.sub i 26ul))
  else if U32.lte i 61ul then uint32_to_uint8 (U32.add 0x30ul (U32.sub i 52ul))
  else if U32.eq i 62ul then uint32_to_uint8 0x2Bul
  else uint32_to_uint8 0x2Ful

(** [unbase64 c] decodes a base64 char to 0..63. *)
let unbase64 (c: U8.t) : Tot opt_u32 =
  let c32 = uint8_to_uint32 c in
  if U32.lte 0x41ul c32 && U32.lte c32 0x5Aul then OU_Some (U32.sub c32 0x41ul)
  else if U32.lte 0x61ul c32 && U32.lte c32 0x7Aul then OU_Some (U32.add (U32.sub c32 0x61ul) 26ul)
  else if U32.lte 0x30ul c32 && U32.lte c32 0x39ul then OU_Some (U32.add (U32.sub c32 0x30ul) 52ul)
  else if U32.eq c32 0x2Bul then OU_Some 62ul
  else if U32.eq c32 0x2Ful then OU_Some 63ul
  else OU_None

(** [is_pad_u8 c] is true when c is '=' (0x3D). *)
let is_pad_u8 (c: U8.t) : bool = U8.eq c 0x3Duy

(** [is_any_pad_u8 c0 c1] — true when either byte is the '=' pad. *)
let is_any_pad_u8 (c0 c1: U8.t) : bool = is_pad_u8 c0 || is_pad_u8 c1

(** [is_pad_pair c2 c3] — true when both c2 and c3 are '=' pads (pad_count = 2). *)
let is_pad_pair (c2 c3: U8.t) : bool = is_pad_u8 c2 && is_pad_u8 c3

(** [is_single_pad c2 c3] — true when exactly one of c2/c3 is '=' (pad_count = 1). *)
let is_single_pad (c2 c3: U8.t) : bool =
  (is_pad_u8 c2 && not (is_pad_u8 c3)) || (is_pad_u8 c3 && not (is_pad_u8 c2))

(* ── Pure decode specs (noextract: mirror the `fn` bodies exactly) ─── *)

(** [decode_base16_spec chars] — the pure spec for [decode_base16]. *)
noextract
let decode_base16_spec (chars: Seq.seq U8.t) : opt_result_u8 =
  if Seq.length chars < 2 then OR8_None
  else
    let c0 = Seq.index chars 0 in
    let c1 = Seq.index chars 1 in
    match unhex c0, unhex c1 with
    | ON_Some hi, ON_Some lo ->
      OR8_Some (U8.uint_to_t (U32.v hi * 16 + U32.v lo), 2ul)
    | _ -> OR8_None

(** [decode_base64_quad_spec chars] — the pure spec for [decode_base64_quad]. *)
noextract
let decode_base64_quad_spec (chars: Seq.seq U8.t) : opt_result_bytes =
  if Seq.length chars < 4 then ORB_None
  else
    let c0 = Seq.index chars 0 in
    let c1 = Seq.index chars 1 in
    let c2 = Seq.index chars 2 in
    let c3 = Seq.index chars 3 in
    if is_any_pad_u8 c0 c1 then ORB_None
    else
      match unbase64 c0, unbase64 c1 with
      | OU_Some v0, OU_Some v1 ->
        let b0 = U8.uint_to_t (U32.v v0 * 4 + U32.v v1 / 16) in
        if is_pad_pair c2 c3 then ORB_Some ({ n = 1ul; b0 = b0; b1 = 0uy; b2 = 0uy })
        else if is_pad_u8 c2 then ORB_None
        else
          (match unbase64 c2 with
           | OU_Some v2 ->
             let b1 = U8.uint_to_t ((U32.v v1 % 16) * 16 + U32.v v2 / 4) in
             if is_single_pad c2 c3 then ORB_Some ({ n = 2ul; b0 = b0; b1 = b1; b2 = 0uy })
             else if is_pad_u8 c3 then ORB_None
             else
               (match unbase64 c3 with
                | OU_Some v3 ->
                  let b2 = U8.uint_to_t ((U32.v v2 % 4) * 64 + U32.v v3) in
                  ORB_Some ({ n = 3ul; b0 = b0; b1 = b1; b2 = b2 })
                | _ -> ORB_None)
           | _ -> ORB_None)
      | _ -> ORB_None

(* ── Pure spec roundtrip lemmas (noextract) ─────────────────────── *)

(** [lemma_decode_base16_spec_roundtrip b] — the spec decodes its own encoding. *)
noextract
let lemma_decode_base16_spec_roundtrip (b: U8.t) : Lemma
  (decode_base16_spec (Seq.seq_of_list (B16.encode_base16 [b])) == OR8_Some (b, 2ul))
  =
  let bs = B16.encode_base16 [b] in
  B16.lemma_encode_base16_single b;
  assert (Seq.length (Seq.seq_of_list bs) >= 2);
  let hi = Seq.index (Seq.seq_of_list bs) 0 in
  let lo = Seq.index (Seq.seq_of_list bs) 1 in
  assert (unhex hi == ON_Some (U32.uint_to_t (U8.v b / 16)));
  assert (unhex lo == ON_Some (U32.uint_to_t (U8.v b % 16)))

(** [lemma_decode_base64_spec_roundtrip_triple] — 3-byte spec roundtrip. *)
noextract
let lemma_decode_base64_spec_roundtrip_triple (b0 b1 b2: U8.t) : Lemma
  (decode_base64_quad_spec (Seq.seq_of_list (B64.encode_base64 [b0; b1; b2]))
   == ORB_Some ({ n = 3ul; b0 = b0; b1 = b1; b2 = b2 }))
  = B64.lemma_base64_triple b0 b1 b2

(** [lemma_decode_base64_spec_roundtrip_tail1] — 1-byte spec roundtrip. *)
noextract
let lemma_decode_base64_spec_roundtrip_tail1 (b0: U8.t) : Lemma
  (decode_base64_quad_spec (Seq.seq_of_list (B64.encode_base64 [b0]))
   == ORB_Some ({ n = 1ul; b0 = b0; b1 = 0uy; b2 = 0uy }))
  = B64.lemma_base64_single b0

(** [lemma_decode_base64_spec_roundtrip_tail2] — 2-byte spec roundtrip. *)
noextract
let lemma_decode_base64_spec_roundtrip_tail2 (b0 b1: U8.t) : Lemma
  (decode_base64_quad_spec (Seq.seq_of_list (B64.encode_base64 [b0; b1]))
   == ORB_Some ({ n = 2ul; b0 = b0; b1 = b1; b2 = 0uy }))
  = B64.lemma_base64_pair b0 b1


(** [lemma_hex_digit_eq_nibble] bridges [hex_digit] to pure
    [nibble_to_upper_hex]. *)
let lemma_hex_digit_eq_nibble (n: nat{n < 16}) : Lemma
  (hex_digit (U32.uint_to_t n) == nibble_to_upper_hex n)
  = if n < 10 then begin
    assert (hex_digit (U32.uint_to_t n) == U8.uint_to_t (n + 48));
    assert (nibble_to_upper_hex n == U8.uint_to_t (0x30 + n))
    end else begin
    assert (hex_digit (U32.uint_to_t n) == U8.uint_to_t (n + 55));
    assert (nibble_to_upper_hex n == U8.uint_to_t (0x37 + n))
    end

(** [lemma_b64_val_i_eq_b64_val] bridges [b64_val_i] to pure [b64_val]. *)
let lemma_b64_val_i_eq_b64_val (n: nat{n < 64}) : Lemma
  (b64_val_i (U32.uint_to_t n) == b64_val n)
  = if n <= 25 then
      assert (b64_val_i (U32.uint_to_t n) == U8.uint_to_t (0x41 + n))
    else if n <= 51 then
      assert (b64_val_i (U32.uint_to_t n) == U8.uint_to_t (0x61 + n - 26))
    else if n <= 61 then
      assert (b64_val_i (U32.uint_to_t n) == U8.uint_to_t (0x30 + n - 52))
    else if n = 62 then
      assert (b64_val_i (U32.uint_to_t n) == U8.uint_to_t 0x2B)
    else
      assert (b64_val_i (U32.uint_to_t n) == U8.uint_to_t 0x2F)

(** [lemma_hex_roundtrip n] proves that for n < 16, hex_digit then unhex
    returns the original value. *)
let lemma_hex_roundtrip (n: U32.t) : Lemma
  (requires U32.lt n 16ul)
  (ensures unhex (hex_digit n) == ON_Some n)
  = let v = U32.v n in
    let hd = hex_digit n in
    let hd_v = U8.v hd in
    if v < 10 then begin
      assert (hd_v == v + 48);
      assert (48 <= hd_v /\ hd_v <= 57);
      assert (U32.uint_to_t (hd_v - 48) == n)
    end else begin
      assert (hd_v == v + 55);
      assert (65 <= hd_v /\ hd_v <= 70);
      assert (U32.uint_to_t (hd_v - 55) == n)
    end

(* ── Encode functions — each with full byte-level post-condition ─────── *)

(** [encode_base16] writes 2 hex chars from a single byte.

    Post-condition references the pure [Data.BaseN.Base16.encode_base16 [b]].

    @param b The single byte to write as two hex chars.
    @param buf The destination buffer (must hold at least 2 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [2ul]). *)
fn encode_base16 (b: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 2 <= A.length buf /\ U32.v off + 1 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 2 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.slice s1 (U32.v off) (U32.v off + 2)
                `Seq.equal` Seq.seq_of_list (B16.encode_base16 [b]))) **
      pure (w == 2ul)
{
  let v = uint8_to_uint32 b;
  let hi = U32.div v 16ul;
  let lo = U32.rem v 16ul;
  lemma_hex_digit_eq_nibble (U32.v hi);
  lemma_hex_digit_eq_nibble (U32.v lo);
  let hi_b = hex_digit hi;
  let lo_b = hex_digit lo;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  A.pts_to_len buf;
  buf.(j0) <- hi_b;
  buf.(j1) <- lo_b;
  2ul
}

(** [encode_base64_triple] writes 4 base64 chars from three bytes.

    Post-condition references the pure [Data.BaseN.Base64.encode_base64 [b0;b1;b2]].

    @param b0 b1 b2 The three bytes to encode.
    @param buf The destination buffer (must hold at least 4 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [4ul]). *)
fn encode_base64_triple (b0 b1 b2: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 4 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.slice s1 (U32.v off) (U32.v off + 4)
                `Seq.equal` Seq.seq_of_list (B64.encode_base64 [b0; b1; b2]))) **
      pure (w == 4ul)
{
  let v0 = uint8_to_uint32 b0;
  let v1 = uint8_to_uint32 b1;
  let v2 = uint8_to_uint32 b2;
  let c0 = U32.div v0 4ul;
  let c1 = U32.add (U32.mul (U32.rem v0 4ul) 16ul) (U32.div v1 16ul);
  let c2 = U32.add (U32.mul (U32.rem v1 16ul) 4ul) (U32.div v2 64ul);
  let c3 = U32.rem v2 64ul;
  lemma_b64_val_i_eq_b64_val (U32.v c0);
  lemma_b64_val_i_eq_b64_val (U32.v c1);
  lemma_b64_val_i_eq_b64_val (U32.v c2);
  lemma_b64_val_i_eq_b64_val (U32.v c3);
  let b0' = b64_val_i c0;
  let b1' = b64_val_i c1;
  let b2' = b64_val_i c2;
  let b3' = b64_val_i c3;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  A.pts_to_len buf;
  buf.(j0) <- b0';
  buf.(j1) <- b1';
  buf.(j2) <- b2';
  buf.(j3) <- b3';
  4ul
}

(** [encode_base64_tail1] writes 4 chars from a single byte + "==" padding.

    @param b0 The byte to encode.
    @param buf The destination buffer (must hold at least 4 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [4ul]). *)
fn encode_base64_tail1 (b0: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 4 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.slice s1 (U32.v off) (U32.v off + 4)
                `Seq.equal` Seq.seq_of_list (B64.encode_base64 [b0]))) **
      pure (w == 4ul)
{
  let v0 = uint8_to_uint32 b0;
  let c0 = U32.div v0 4ul;
  let c1 = U32.mul (U32.rem v0 4ul) 16ul;
  lemma_b64_val_i_eq_b64_val (U32.v c0);
  lemma_b64_val_i_eq_b64_val (U32.v c1);
  let b0' = b64_val_i c0;
  let b1' = b64_val_i c1;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  A.pts_to_len buf;
  buf.(j0) <- b0';
  buf.(j1) <- b1';
  buf.(j2) <- pad_byte;
  buf.(j3) <- pad_byte;
  4ul
}

(** [encode_base64_tail2] writes 4 chars from two bytes + "=" padding.

    @param b0 b1 The two bytes to encode.
    @param buf The destination buffer (must hold at least 4 bytes at [off]).
    @param off The write offset.
    @returns The number of bytes written (always [4ul]). *)
fn encode_base64_tail2 (b0 b1: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 4 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.slice s1 (U32.v off) (U32.v off + 4)
                `Seq.equal` Seq.seq_of_list (B64.encode_base64 [b0; b1]))) **
      pure (w == 4ul)
{
  let v0 = uint8_to_uint32 b0;
  let v1 = uint8_to_uint32 b1;
  let c0 = U32.div v0 4ul;
  let c1 = U32.add (U32.mul (U32.rem v0 4ul) 16ul) (U32.div v1 16ul);
  let c2 = U32.mul (U32.rem v1 16ul) 4ul;
  lemma_b64_val_i_eq_b64_val (U32.v c0);
  lemma_b64_val_i_eq_b64_val (U32.v c1);
  lemma_b64_val_i_eq_b64_val (U32.v c2);
  let b0' = b64_val_i c0;
  let b1' = b64_val_i c1;
  let b2' = b64_val_i c2;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  A.pts_to_len buf;
  buf.(j0) <- b0';
  buf.(j1) <- b1';
  buf.(j2) <- b2';
  buf.(j3) <- pad_byte;
  4ul
}

(* ── Decode functions — each with result-level post-condition ───────── *)

(** [decode_base16] decodes 2 hex chars → 1 byte.

    Result matches the pure [Data.BaseN.Base16.decode_base16] of the 2 chars.

    @param buf The source buffer (must hold at least 2 bytes at [off]).
    @param off The read offset.
    @returns [OR8_Some (b, 2ul)] on valid hex pair, [OR8_None] otherwise. *)
fn decode_base16 (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 2 <= A.length buf /\ U32.v off + 1 < 4294967296)
    returns r: opt_result_u8
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 2 <= A.length buf /\
        r == decode_base16_spec (Seq.slice s0 (U32.v off) (U32.v off + 2)))
{
  A.pts_to_len buf;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let c0 = buf.(j0);
  let c1 = buf.(j1);
  let r0 = unhex c0;
  let r1 = unhex c1;
  match r0 {
    ON_None -> { OR8_None }
    ON_Some hi -> {
      match r1 {
        ON_None -> { OR8_None }
        ON_Some lo -> {
          let v = U32.add (U32.mul hi 16ul) lo;
          OR8_Some (uint32_to_uint8 v, 2ul)
        }
      }
    }
  }
}

(** [decode_base64_quad] decodes 4 base64 chars → up to 3 bytes.

    RFC 4648 allows pad_count in {0, 1, 2}.  Result matches the pure
    [Data.BaseN.Base64.decode_base64] of the 4 chars.

    @param buf The source buffer (must hold at least 4 bytes at [off]).
    @param off The read offset.
    @returns [ORB_Some (bytes, 4ul)] on success, [ORB_None] otherwise. *)
fn decode_base64_quad (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns r: opt_result_bytes
    ensures
      A.pts_to buf s0 **
      pure (
        A.length buf == Seq.length s0 /\
        U32.v off + 4 <= A.length buf /\
        r == decode_base64_quad_spec (Seq.slice s0 (U32.v off) (U32.v off + 4)))
{
  A.pts_to_len buf;
  let j0 = US.uint32_to_sizet off;
  let j1 = US.uint32_to_sizet (U32.add off 1ul);
  let j2 = US.uint32_to_sizet (U32.add off 2ul);
  let j3 = US.uint32_to_sizet (U32.add off 3ul);
  let c0 = buf.(j0);
  let c1 = buf.(j1);
  let c2 = buf.(j2);
  let c3 = buf.(j3);
  if is_any_pad_u8 c0 c1 {
    ORB_None
  } else {
    let r0 = unbase64 c0;
    let r1 = unbase64 c1;
    match r0 {
      OU_None -> { ORB_None }
      OU_Some v0 -> {
        match r1 {
          OU_None -> { ORB_None }
          OU_Some v1 -> {
            let b0 = uint32_to_uint8 (U32.add (U32.mul v0 4ul) (U32.div v1 16ul));
            if is_pad_pair c2 c3 {
              ORB_Some ({ n = 1ul; b0 = b0; b1 = 0uy; b2 = 0uy })
            } else if is_pad_u8 c2 {
              ORB_None
            } else {
              let r2 = unbase64 c2;
              match r2 {
                OU_None -> { ORB_None }
                OU_Some v2 -> {
                  let b1 = uint32_to_uint8 (U32.add (U32.mul (U32.rem v1 16ul) 16ul) (U32.div v2 4ul));
                  if is_single_pad c2 c3 {
                    ORB_Some ({ n = 2ul; b0 = b0; b1 = b1; b2 = 0uy })
                  } else if is_pad_u8 c3 {
                    ORB_None
                  } else {
                    let r3 = unbase64 c3;
                    match r3 {
                      OU_None -> { ORB_None }
                      OU_Some v3 -> {
                        let b2 = uint32_to_uint8 (U32.add (U32.mul (U32.rem v2 4ul) 64ul) v3);
                        ORB_Some ({ n = 3ul; b0 = b0; b1 = b1; b2 = b2 })
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

(* ── Value-preserving roundtrip lemmas ──────────────────────────────── *)

(** [lemma_pulse_base16_roundtrip]: encode then decode preserves the value.

    @param b The byte to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode_base16 buf off] after [encode_base16 b buf off]
    returns [OR8_Some (b, 2ul)]. *)
fn lemma_pulse_base16_roundtrip (b: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 2 <= A.length buf /\ U32.v off + 1 < 4294967296)
    returns res: (U32.t & opt_result_u8)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 2ul /\ snd res == OR8_Some (b, 2ul))
{
  let n = encode_base16 b buf off;
  let r = decode_base16 buf off;
  lemma_decode_base16_spec_roundtrip b;
  (n, r)
}

(** [lemma_pulse_base64_triple_roundtrip]: encode then decode preserves 3 bytes.

    @param b0 b1 b2 The three bytes to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode_base64_quad buf off] after [encode_base64_triple b0 b1 b2 buf off]
    returns [ORB_Some ([b0;b1;b2], 4ul)]. *)
fn lemma_pulse_base64_triple_roundtrip (b0 b1 b2: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns res: (U32.t & opt_result_bytes)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 4ul /\ snd res == ORB_Some ({ n = 3ul; b0 = b0; b1 = b1; b2 = b2 }))
{
  let n = encode_base64_triple b0 b1 b2 buf off;
  let r = decode_base64_quad buf off;
  lemma_decode_base64_spec_roundtrip_triple b0 b1 b2;
  (n, r)
}

(** [lemma_pulse_base64_tail1_roundtrip]: encode then decode preserves 1 byte.

    @param b0 The byte to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode_base64_quad buf off] after [encode_base64_tail1 b0 buf off]
    returns [ORB_Some ([b0], 4ul)]. *)
fn lemma_pulse_base64_tail1_roundtrip (b0: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns res: (U32.t & opt_result_bytes)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 4ul /\ snd res == ORB_Some ({ n = 1ul; b0 = b0; b1 = 0uy; b2 = 0uy }))
{
  let n = encode_base64_tail1 b0 buf off;
  let r = decode_base64_quad buf off;
  lemma_decode_base64_spec_roundtrip_tail1 b0;
  (n, r)
}

(** [lemma_pulse_base64_tail2_roundtrip]: encode then decode preserves 2 bytes.

    @param b0 b1 The two bytes to roundtrip.
    @param buf The buffer.
    @param off The offset.
    Proves [decode_base64_quad buf off] after [encode_base64_tail2 b0 b1 buf off]
    returns [ORB_Some ([b0;b1], 4ul)]. *)
fn lemma_pulse_base64_tail2_roundtrip (b0 b1: U8.t) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires
      A.pts_to buf s0 **
      pure (U32.v off + 4 <= A.length buf /\ U32.v off + 3 < 4294967296)
    returns res: (U32.t & opt_result_bytes)
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1) **
      pure (fst res == 4ul /\ snd res == ORB_Some ({ n = 2ul; b0 = b0; b1 = b1; b2 = 0uy }))
{
  let n = encode_base64_tail2 b0 b1 buf off;
  let r = decode_base64_quad buf off;
  lemma_decode_base64_spec_roundtrip_tail2 b0 b1;
  (n, r)
}
