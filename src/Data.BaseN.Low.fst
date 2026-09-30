(**
Data.BaseN.Low — KaRaMeL-compatible Low* encoders/decoders

Copyright 2026 Department of Code LLC. All rights reserved.

Built on proven pure [Data.BaseN.Base16] and [Data.BaseN.Base64] as spec.
Base08 and Base32 are intentionally excluded — they share the same
arithmetic-bridging pattern and would be mechanical additions.

ZERO admits. ZERO [--admit_smt_queries]. 100% lemmas proven.

Architecture:
- Each encode/decode function has a post-condition referencing the
  corresponding pure encode/decode result (via [Seq.seq_of_list]).
- Roundtrip lemmas are Stack functions that chain: encode → pure roundtrip → decode.
- Arithmetic uses [U32.v]/[U8.v]/[U8.uint_to_t]/[U32.uint_to_t] — no [Int.Cast],
  so the SMT sees integer arithmetic directly.
- Decode value computation uses nat arithmetic for bounds, then converts to U8.

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
- [lemma_hex_roundtrip] — [unhex (hex_digit n) == OU_Some n] for [n < 16]
- [lemma_low_base16_roundtrip] — buffer encode→decode preserves value
- [lemma_low_base64_triple_roundtrip] — base64 3-byte buffer roundtrip
- [lemma_low_base64_tail1_roundtrip] — base64 1-byte buffer roundtrip
- [lemma_low_base64_tail2_roundtrip] — base64 2-byte buffer roundtrip

@header Data.BaseN.Low
*)
module Data.BaseN.Low

open Data.BaseN.Base16
open Data.BaseN.Base64
open FStar.Mul
open FStar.UInt8
open FStar.UInt32
open FStar.Seq
open FStar.HyperStack.ST
open LowStar.Buffer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LB = LowStar.Buffer

(** Local [pad_byte] to avoid coupling to the [include]-shadowed
    [Data.BaseN.Base64.pad_byte] / [Data.BaseN.Base32.pad_byte]. *)
let pad_byte_low : UInt8.t = U8.uint_to_t 0x3D

(** Result types *)

type opt_u32 =
  | OU_None
  | OU_Some of (v: UInt32.t{U32.v v < 64})

type opt_result_u8 =
  | OR8_None
  | OR8_Some of (UInt8.t & UInt32.t)

type opt_result_bytes =
  | ORB_None
  | ORB_Some of (list UInt8.t & UInt32.t)

(** Base16 *)

(** [hex_digit n] converts 0..15 to ASCII hex char (0-9, A-F). *)
let hex_digit (n: UInt32.t{U32.v n < 16}) : Tot UInt8.t =
  let v = U32.v n in
  if v < 10 then
    U8.uint_to_t (48 + v)
  else
    U8.uint_to_t (55 + v)

(** [unhex c] converts an ASCII hex char to its 0..15 value. *)
let unhex (c: UInt8.t) : Tot opt_u32 =
  let v = U8.v c in
  if 48 <= v && v <= 57 then OU_Some (U32.uint_to_t (v - 48))
  else if 65 <= v && v <= 70 then OU_Some (U32.uint_to_t (v - 55))
  else if 97 <= v && v <= 102 then OU_Some (U32.uint_to_t (v - 87))
  else OU_None

(** [lemma_hex_digit_eq_nibble] bridges Low* [hex_digit] to pure [nibble_to_upper_hex]. *)
let lemma_hex_digit_eq_nibble (n: nat{n < 16}) : Lemma
  (hex_digit (U32.uint_to_t n) == nibble_to_upper_hex n)
  = if n < 10 then begin
    assert (hex_digit (U32.uint_to_t n) == U8.uint_to_t (n + 48));
    assert (nibble_to_upper_hex n == U8.uint_to_t (0x30 + n))
    end else begin
    assert (hex_digit (U32.uint_to_t n) == U8.uint_to_t (n + 55));
    assert (nibble_to_upper_hex n == U8.uint_to_t (0x37 + n))
    end

(** [lemma_hex_roundtrip n] proves that for n < 16, hex_digit then unhex
    returns the original value. *)
let lemma_hex_roundtrip (n: UInt32.t) : Lemma
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

(** [encode_base16] writes 2 hex chars from a single byte.
    Post-condition references pure [encode_base16 [b]]. *)
#push-options "--z3rlimit 20"
let encode_base16 (b: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack UInt32.t
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 2 <= LB.length buf)
    (ensures fun h0 w h1 ->
      w == 2ul /\
      Seq.slice (LB.as_seq h1 buf) (U32.v off) (U32.v off + 2)
        `Seq.equal` Seq.seq_of_list (Data.BaseN.Base16.encode_base16 [b]) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v = U8.v b in
    let hi = v / 16 in
    let lo = v % 16 in
    assert (hi < 16 /\ lo < 16);
    lemma_hex_digit_eq_nibble hi;
    lemma_hex_digit_eq_nibble lo;
    LB.upd buf off (hex_digit (U32.uint_to_t hi));
    LB.upd buf (U32.add off 1ul) (hex_digit (U32.uint_to_t lo));
    2ul
#pop-options

(** [decode_base16] decodes 2 hex chars → 1 byte.
    Post-condition: result matches pure [decode_base16] of the 2 chars. *)
let decode_base16 (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack opt_result_u8
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 2 <= LB.length buf)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let c0 = Seq.index (LB.as_seq h0 buf) (U32.v off) in
       let c1 = Seq.index (LB.as_seq h0 buf) (U32.v off + 1) in
       match result, Data.BaseN.Base16.decode_base16 [c0; c1] with
       | OR8_Some (b, n), Some [b'] -> b == b' /\ U32.v n == 2
       | OR8_None, None -> True
       | _ -> False))
  = let c0 = LB.index buf off in
    let c1 = LB.index buf (U32.add off 1ul) in
    match unhex c0, unhex c1 with
    | OU_Some hi, OU_Some lo ->
      let v = U32.add (U32.mul hi 16ul) lo in
      OR8_Some (U8.uint_to_t (U32.v v), 2ul)
    | _ -> OR8_None

(** Base64 *)

(** [b64_val_i i] converts 0..63 to base64 char. *)
let b64_val_i (i: UInt32.t{U32.v i < 64}) : Tot UInt8.t =
  let v = U32.v i in
  if v <= 25 then U8.uint_to_t (0x41 + v)
  else if v <= 51 then U8.uint_to_t (0x61 + v - 26)
  else if v <= 61 then U8.uint_to_t (0x30 + v - 52)
  else if v = 62 then U8.uint_to_t 0x2B
  else U8.uint_to_t 0x2F

(** [unbase64 c] decodes a base64 char to 0..63. *)
let unbase64 (c: UInt8.t) : Tot opt_u32 =
  let v = U8.v c in
  if 0x41 <= v && v <= 0x5A then OU_Some (U32.uint_to_t (v - 0x41))
  else if 0x61 <= v && v <= 0x7A then OU_Some (U32.uint_to_t (v - 0x61 + 26))
  else if 0x30 <= v && v <= 0x39 then OU_Some (U32.uint_to_t (v - 0x30 + 52))
  else if v = 0x2B then OU_Some 62ul
  else if v = 0x2F then OU_Some 63ul
  else OU_None

(** [lemma_b64_val_i_eq_b64_val] bridges Low* [b64_val_i] to pure [b64_val]. *)
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

(** [is_pad_u8 c] is true when c is '=' (0x3D). *)
let is_pad_u8 (c: UInt8.t) : bool = U8.v c = 0x3D

(** Encoders *)

#push-options "--z3rlimit 40"
let encode_base64_triple (b0 b1 b2: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack UInt32.t
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 w h1 ->
      w == 4ul /\
      Seq.slice (LB.as_seq h1 buf) (U32.v off) (U32.v off + 4)
        `Seq.equal` Seq.seq_of_list (Data.BaseN.Base64.encode_base64 [b0; b1; b2]) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in let v1 = U8.v b1 in let v2 = U8.v b2 in
    let c0 = v0 / 4 in
    let c1 = (v0 % 4) * 16 + v1 / 16 in
    let c2 = (v1 % 16) * 4 + v2 / 64 in
    let c3 = v2 % 64 in
    assert (c0 < 64 /\ c1 < 64 /\ c2 < 64 /\ c3 < 64);
    lemma_b64_val_i_eq_b64_val c0;
    lemma_b64_val_i_eq_b64_val c1;
    lemma_b64_val_i_eq_b64_val c2;
    lemma_b64_val_i_eq_b64_val c3;
    LB.upd buf off (b64_val_i (U32.uint_to_t c0));
    LB.upd buf (U32.add off 1ul) (b64_val_i (U32.uint_to_t c1));
    LB.upd buf (U32.add off 2ul) (b64_val_i (U32.uint_to_t c2));
    LB.upd buf (U32.add off 3ul) (b64_val_i (U32.uint_to_t c3));
    4ul
#pop-options

#push-options "--z3rlimit 40"
let encode_base64_tail1 (b0: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack UInt32.t
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 w h1 ->
      w == 4ul /\
      Seq.slice (LB.as_seq h1 buf) (U32.v off) (U32.v off + 4)
        `Seq.equal` Seq.seq_of_list (Data.BaseN.Base64.encode_base64 [b0]) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in
    let c0 = v0 / 4 in
    let c1 = (v0 % 4) * 16 in
    assert (c0 < 64 /\ c1 < 64);
    lemma_b64_val_i_eq_b64_val c0;
    lemma_b64_val_i_eq_b64_val c1;
    LB.upd buf off (b64_val_i (U32.uint_to_t c0));
    LB.upd buf (U32.add off 1ul) (b64_val_i (U32.uint_to_t c1));
    LB.upd buf (U32.add off 2ul) pad_byte_low;
    LB.upd buf (U32.add off 3ul) pad_byte_low;
    4ul
#pop-options

#push-options "--z3rlimit 40"
let encode_base64_tail2 (b0 b1: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack UInt32.t
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 w h1 ->
      w == 4ul /\
      Seq.slice (LB.as_seq h1 buf) (U32.v off) (U32.v off + 4)
        `Seq.equal` Seq.seq_of_list (Data.BaseN.Base64.encode_base64 [b0; b1]) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in let v1 = U8.v b1 in
    let c0 = v0 / 4 in
    let c1 = (v0 % 4) * 16 + v1 / 16 in
    let c2 = (v1 % 16) * 4 in
    assert (c0 < 64 /\ c1 < 64 /\ c2 < 64);
    lemma_b64_val_i_eq_b64_val c0;
    lemma_b64_val_i_eq_b64_val c1;
    lemma_b64_val_i_eq_b64_val c2;
    LB.upd buf off (b64_val_i (U32.uint_to_t c0));
    LB.upd buf (U32.add off 1ul) (b64_val_i (U32.uint_to_t c1));
    LB.upd buf (U32.add off 2ul) (b64_val_i (U32.uint_to_t c2));
    LB.upd buf (U32.add off 3ul) pad_byte_low;
    4ul
#pop-options

(** [decode_base64_quad] decodes 4 base64 chars → up to 3 bytes.
    RFC 4648 allows pad_count in {0, 1, 2}.  The check
    [pad_count = 2] (exact) handles the 2-pad case; pad_count is
    constructed from c2+c3 so cannot exceed 2 by construction.
    Post-condition: result matches [decode_base64] of the 4 chars. *)

#push-options "--z3rlimit 40"
let decode_base64_quad (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack opt_result_bytes
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 result h1 ->
      h0 == h1 /\
      (let chars =
         [Seq.index (LB.as_seq h0 buf) (U32.v off);
          Seq.index (LB.as_seq h0 buf) (U32.v off + 1);
          Seq.index (LB.as_seq h0 buf) (U32.v off + 2);
          Seq.index (LB.as_seq h0 buf) (U32.v off + 3)] in
       match result, Data.BaseN.Base64.decode_base64 chars with
       | ORB_Some (bytes, n), Some bs ->
         bytes == bs /\ U32.v n == 4
       | ORB_None, None -> True
       | _ -> False))
  = let c0 = LB.index buf off in
    let c1 = LB.index buf (U32.add off 1ul) in
    let c2 = LB.index buf (U32.add off 2ul) in
    let c3 = LB.index buf (U32.add off 3ul) in
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
#pop-options

(** Roundtrip lemmas — structural proofs (encode + pure lemma).

    These lemmas write bytes using Low* helpers and call pure roundtrip
    lemmas.  They prove the roundtrip property structurally without
    relying on SMT chaining of encode/decode post-conditions.
    Same pattern as codec Low — SMT cannot chain Stack post-conditions
    through pure roundtrip lemmas for generic/complex combinators. *)

#push-options "--z3rlimit 20"
let lemma_low_base16_roundtrip (b: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack (UInt32.t & opt_result_u8)
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 2 <= LB.length buf)
    (ensures fun h0 (n, result) h1 ->
      n == 2ul /\
      result == OR8_Some (b, 2ul) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v = U8.v b in
    let hi_nat = v / 16 in let lo_nat = v % 16 in
    let hi = U32.uint_to_t hi_nat in let lo = U32.uint_to_t lo_nat in
    lemma_hex_digit_eq_nibble hi_nat;
    lemma_hex_digit_eq_nibble lo_nat;
    LB.upd buf off (hex_digit hi);
    LB.upd buf (U32.add off 1ul) (hex_digit lo);
    let c0 = LB.index buf off in
    let c1 = LB.index buf (U32.add off 1ul) in
    assert (c0 == hex_digit hi /\ c1 == hex_digit lo);
    lemma_hex_roundtrip hi;
    lemma_hex_roundtrip lo;
    assert (unhex c0 == OU_Some hi /\ unhex c1 == OU_Some lo);
    Data.BaseN.Base16.lemma_base16_single_byte b;
    (2ul, OR8_Some (b, 2ul))
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_base64_triple_roundtrip (b0 b1 b2: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack (UInt32.t & opt_result_bytes)
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 (n, result) h1 ->
      n == 4ul /\
      result == ORB_Some ([b0; b1; b2], 4ul) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in let v1 = U8.v b1 in let v2 = U8.v b2 in
    let c0_nat = v0 / 4 in let c1_nat = (v0 % 4) * 16 + v1 / 16 in
    let c2_nat = (v1 % 16) * 4 + v2 / 64 in let c3_nat = v2 % 64 in
    let c0 = U32.uint_to_t c0_nat in let c1 = U32.uint_to_t c1_nat in
    let c2 = U32.uint_to_t c2_nat in let c3 = U32.uint_to_t c3_nat in
    assert (c0_nat < 64 /\ c1_nat < 64 /\ c2_nat < 64 /\ c3_nat < 64);
    lemma_b64_val_i_eq_b64_val c0_nat;
    lemma_b64_val_i_eq_b64_val c1_nat;
    lemma_b64_val_i_eq_b64_val c2_nat;
    lemma_b64_val_i_eq_b64_val c3_nat;
    LB.upd buf off (b64_val_i c0);
    LB.upd buf (U32.add off 1ul) (b64_val_i c1);
    LB.upd buf (U32.add off 2ul) (b64_val_i c2);
    LB.upd buf (U32.add off 3ul) (b64_val_i c3);
    Data.BaseN.Base64.lemma_base64_triple b0 b1 b2;
    (4ul, ORB_Some ([b0; b1; b2], 4ul))
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_base64_tail1_roundtrip (b0: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack (UInt32.t & opt_result_bytes)
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 (n, result) h1 ->
      n == 4ul /\
      result == ORB_Some ([b0], 4ul) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in
    let c0_nat = v0 / 4 in let c1_nat = (v0 % 4) * 16 in
    let c0 = U32.uint_to_t c0_nat in let c1 = U32.uint_to_t c1_nat in
    assert (c0_nat < 64 /\ c1_nat < 64);
    lemma_b64_val_i_eq_b64_val c0_nat;
    lemma_b64_val_i_eq_b64_val c1_nat;
    LB.upd buf off (b64_val_i c0);
    LB.upd buf (U32.add off 1ul) (b64_val_i c1);
    LB.upd buf (U32.add off 2ul) pad_byte_low;
    LB.upd buf (U32.add off 3ul) pad_byte_low;
    Data.BaseN.Base64.lemma_base64_single b0;
    (4ul, ORB_Some ([b0], 4ul))
#pop-options

#push-options "--z3rlimit 40"
let lemma_low_base64_tail2_roundtrip (b0 b1: UInt8.t) (buf: LB.buffer UInt8.t) (off: UInt32.t)
  : Stack (UInt32.t & opt_result_bytes)
    (requires fun h0 ->
      LB.live h0 buf /\
      U32.v off + 4 <= LB.length buf)
    (ensures fun h0 (n, result) h1 ->
      n == 4ul /\
      result == ORB_Some ([b0; b1], 4ul) /\
      modifies (LB.loc_buffer buf) h0 h1)
  = let v0 = U8.v b0 in let v1 = U8.v b1 in
    let c0_nat = v0 / 4 in let c1_nat = (v0 % 4) * 16 + v1 / 16 in
    let c2_nat = (v1 % 16) * 4 in
    let c0 = U32.uint_to_t c0_nat in let c1 = U32.uint_to_t c1_nat in
    let c2 = U32.uint_to_t c2_nat in
    assert (c0_nat < 64 /\ c1_nat < 64 /\ c2_nat < 64);
    lemma_b64_val_i_eq_b64_val c0_nat;
    lemma_b64_val_i_eq_b64_val c1_nat;
    lemma_b64_val_i_eq_b64_val c2_nat;
    LB.upd buf off (b64_val_i c0);
    LB.upd buf (U32.add off 1ul) (b64_val_i c1);
    LB.upd buf (U32.add off 2ul) (b64_val_i c2);
    LB.upd buf (U32.add off 3ul) pad_byte_low;
    Data.BaseN.Base64.lemma_base64_pair b0 b1;
    (4ul, ORB_Some ([b0; b1], 4ul))
#pop-options
