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

(** Optional (byte, bytes-written) pair — the base16 decode result. *)
type opt_result_u8 =
  | OR8_None
  | OR8_Some of (b: U8.t & consumed: U32.t)

(** Optional (bytes, bytes-written) pair — the base64 decode result. *)
type opt_result_bytes =
  | ORB_None
  | ORB_Some of (bytes: list U8.t & consumed: U32.t)

(* ── Pure helpers (erased: noextract so Custard skips them) ─────────── *)

(** Local [pad_byte] to avoid coupling to the [open]-shadowed
    [Data.BaseN.Base64.pad_byte] / [Data.BaseN.Base32.pad_byte]. *)
let pad_byte : U8.t = U8.uint_to_t 0x3D

(** [hex_digit n] converts 0..15 to ASCII hex char (0-9, A-F). *)
let hex_digit (n: U32.t{U32.v n < 16}) : Tot U8.t =
  let v = U32.v n in
  if v < 10 then U8.uint_to_t (48 + v) else U8.uint_to_t (55 + v)

(** [unhex c] converts an ASCII hex char to its 0..15 value. *)
let unhex (c: U8.t) : Tot opt_u32 =
  let v = U8.v c in
  if 48 <= v && v <= 57 then OU_Some (U32.uint_to_t (v - 48))
  else if 65 <= v && v <= 70 then OU_Some (U32.uint_to_t (v - 55))
  else if 97 <= v && v <= 102 then OU_Some (U32.uint_to_t (v - 87))
  else OU_None

(** [b64_val_i i] converts 0..63 to base64 char. *)
let b64_val_i (i: U32.t{U32.v i < 64}) : Tot U8.t =
  let v = U32.v i in
  if v <= 25 then U8.uint_to_t (0x41 + v)
  else if v <= 51 then U8.uint_to_t (0x61 + v - 26)
  else if v <= 61 then U8.uint_to_t (0x30 + v - 52)
  else if v = 62 then U8.uint_to_t 0x2B
  else U8.uint_to_t 0x2F

(** [unbase64 c] decodes a base64 char to 0..63. *)
let unbase64 (c: U8.t) : Tot opt_u32 =
  let v = U8.v c in
  if 0x41 <= v && v <= 0x5A then OU_Some (U32.uint_to_t (v - 0x41))
  else if 0x61 <= v && v <= 0x7A then OU_Some (U32.uint_to_t (v - 0x61 + 26))
  else if 0x30 <= v && v <= 0x39 then OU_Some (U32.uint_to_t (v - 0x30 + 52))
  else if v = 0x2B then OU_Some 62ul
  else if v = 0x2F then OU_Some 63ul
  else OU_None

(** [is_pad_u8 c] is true when c is '=' (0x3D). *)
let is_pad_u8 (c: U8.t) : bool = U8.v c = 0x3D

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
  (ensures unhex (hex_digit n) == OU_Some n)
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
  let v = U8.v b;
  let hi = v / 16 in
  let lo = v % 16 in
  lemma_hex_digit_eq_nibble hi;
  lemma_hex_digit_eq_nibble lo;
  let hi_b = hex_digit (U32.uint_to_t hi) in
  let lo_b = hex_digit (U32.uint_to_t lo) in
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
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
  let v0 = U8.v b0 in let v1 = U8.v b1 in let v2 = U8.v b2 in
  let c0 = v0 / 4 in
  let c1 = (v0 % 4) * 16 + v1 / 16 in
  let c2 = (v1 % 16) * 4 + v2 / 64 in
  let c3 = v2 % 64 in
  lemma_b64_val_i_eq_b64_val c0;
  lemma_b64_val_i_eq_b64_val c1;
  lemma_b64_val_i_eq_b64_val c2;
  lemma_b64_val_i_eq_b64_val c3;
  let b0' = b64_val_i (U32.uint_to_t c0) in
  let b1' = b64_val_i (U32.uint_to_t c1) in
  let b2' = b64_val_i (U32.uint_to_t c2) in
  let b3' = b64_val_i (U32.uint_to_t c3) in
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
  let j2 = US.uint32_to_sizet (U32.add off 2ul) in
  let j3 = US.uint32_to_sizet (U32.add off 3ul) in
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
  let v0 = U8.v b0 in
  let c0 = v0 / 4 in
  let c1 = (v0 % 4) * 16 in
  lemma_b64_val_i_eq_b64_val c0;
  lemma_b64_val_i_eq_b64_val c1;
  let b0' = b64_val_i (U32.uint_to_t c0) in
  let b1' = b64_val_i (U32.uint_to_t c1) in
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
  let j2 = US.uint32_to_sizet (U32.add off 2ul) in
  let j3 = US.uint32_to_sizet (U32.add off 3ul) in
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
  let v0 = U8.v b0 in let v1 = U8.v b1 in
  let c0 = v0 / 4 in
  let c1 = (v0 % 4) * 16 + v1 / 16 in
  let c2 = (v1 % 16) * 4 in
  lemma_b64_val_i_eq_b64_val c0;
  lemma_b64_val_i_eq_b64_val c1;
  lemma_b64_val_i_eq_b64_val c2;
  let b0' = b64_val_i (U32.uint_to_t c0) in
  let b1' = b64_val_i (U32.uint_to_t c1) in
  let b2' = b64_val_i (U32.uint_to_t c2) in
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
  let j2 = US.uint32_to_sizet (U32.add off 2ul) in
  let j3 = US.uint32_to_sizet (U32.add off 3ul) in
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
        (let c0 = Seq.index s0 (U32.v off) in
         let c1 = Seq.index s0 (U32.v off + 1) in
         match r, B16.decode_base16 [c0; c1] with
         | OR8_Some (b, n), Some [b'] -> b == b' /\ U32.v n == 2
         | OR8_None, None -> True
         | _ -> False))
{
  A.pts_to_len buf;
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
  let c0 = buf.(j0) in
  let c1 = buf.(j1) in
  match unhex c0, unhex c1 with
  | OU_Some hi, OU_Some lo ->
    let v = U32.add (U32.mul hi 16ul) lo in
    OR8_Some (U8.uint_to_t (U32.v v), 2ul)
  | _ -> OR8_None
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
        (let chars =
           [Seq.index s0 (U32.v off);
            Seq.index s0 (U32.v off + 1);
            Seq.index s0 (U32.v off + 2);
            Seq.index s0 (U32.v off + 3)] in
         match r, B64.decode_base64 chars with
         | ORB_Some (bytes, n), Some bs -> bytes == bs /\ U32.v n == 4
         | ORB_None, None -> True
         | _ -> False))
{
  A.pts_to_len buf;
  let j0 = US.uint32_to_sizet off in
  let j1 = US.uint32_to_sizet (U32.add off 1ul) in
  let j2 = US.uint32_to_sizet (U32.add off 2ul) in
  let j3 = US.uint32_to_sizet (U32.add off 3ul) in
  let c0 = buf.(j0) in
  let c1 = buf.(j1) in
  let c2 = buf.(j2) in
  let c3 = buf.(j3) in
  let pad_count = (if is_pad_u8 c3 then 1 else 0) + (if is_pad_u8 c2 then 1 else 0) in
  if is_pad_u8 c0 || is_pad_u8 c1 then ORB_None
  else
    match unbase64 c0, unbase64 c1 with
    | OU_Some v0, OU_Some v1 ->
      let b0 = U8.uint_to_t (U32.v v0 * 4 + U32.v v1 / 16) in
      if pad_count = 2 then
        ORB_Some ([b0], 4ul)
      else if is_pad_u8 c2 then ORB_None
      else
        (match unbase64 c2 with
         | OU_Some v2 ->
           let b1 = U8.uint_to_t ((U32.v v1 % 16) * 16 + U32.v v2 / 4) in
           if pad_count = 1 then
             ORB_Some ([b0; b1], 4ul)
           else if is_pad_u8 c3 then ORB_None
           else
             (match unbase64 c3 with
              | OU_Some v3 ->
                let b2 = U8.uint_to_t ((U32.v v2 % 4) * 64 + U32.v v3) in
                ORB_Some ([b0; b1; b2], 4ul)
              | _ -> ORB_None)
         | _ -> ORB_None)
    | _ -> ORB_None
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
  B16.lemma_base16_single_byte b;
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
      pure (fst res == 4ul /\ snd res == ORB_Some ([b0; b1; b2], 4ul))
{
  let n = encode_base64_triple b0 b1 b2 buf off;
  let r = decode_base64_quad buf off;
  B64.lemma_base64_triple b0 b1 b2;
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
      pure (fst res == 4ul /\ snd res == ORB_Some ([b0], 4ul))
{
  let n = encode_base64_tail1 b0 buf off;
  let r = decode_base64_quad buf off;
  B64.lemma_base64_single b0;
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
      pure (fst res == 4ul /\ snd res == ORB_Some ([b0; b1], 4ul))
{
  let n = encode_base64_tail2 b0 b1 buf off;
  let r = decode_base64_quad buf off;
  B64.lemma_base64_pair b0 b1;
  (n, r)
}
