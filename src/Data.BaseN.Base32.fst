(**
Data.BaseN.Base32 — RFC 4648 §6 Base32 Encoding

Copyright 2026 Department of Code LLC. All rights reserved.

ZERO admits. ZERO --admit_smt_queries. 100% lemmas proven.

Architecture:
- encode_base32: all cases use explicit cons (no @). Direct bit-slicing
  formulas — structural inverses of decode_base32.
- decode_base32: split into non-recursive decode_base32_group (8 chars →
  option (list byte)) + thin recursive wrapper with explicit cons matching
  (no @). Termination checker sees L.length rest < L.length bs directly.
- Helper lemmas (lemma_b32_byte0..4) prove extraction identities via
  lemma_div_mod, small_div, lemma_mod_plus_distr_l.
- lemma_decode_base32_group_quintet proves group decode of encoded 5-byte block.
- lemma_base32_roundtrip: induction with just two lemma calls per step.
  The cons-based approach eliminates all @ from encode/decode, letting
  the SMT see through the list structure directly.

@header Data.BaseN.Base32
*)
module Data.BaseN.Base32

open Data.Codec.Types
open FStar.UInt8
open FStar.List.Tot
open FStar.Mul
open FStar.Math.Lemmas

module U8 = FStar.UInt8
module L = FStar.List.Tot

(** Base32 alphabet (RFC 4648 §6: A-Z + 2-7) *)

(** [b32_val i] maps a 5-bit value to its RFC 4648 §6 base32 character.
    @param i Integer in [0, 31]. *)
let b32_val (i: int{0 <= i /\ i <= 31}) : Tot byte =
  let u = U8.uint_to_t in
  if i <= 25 then u (0x41 + i) else u (0x32 + i - 26)

(** [base32_char_to_val b] converts a base32 character to its 5-bit value.
    @param b Byte representing a base32 character.
    @returns [Some i] with [0 <= i <= 31], or [None] if [b] is not base32. *)
let base32_char_to_val (b: byte) : option int =
  let v = U8.v b in
  if 0x41 <= v && v <= 0x5A then Some (v - 0x41)
  else if 0x32 <= v && v <= 0x37 then Some (v - 0x32 + 26)
  else None

(** [is_base32_char b] is true when byte [b] is a valid RFC 4648 §6 base32
    character (A-Z, 2-7). Padding (=) is NOT a base32 char. *)
let is_base32_char (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x32 <= v && v <= 0x37)

(** [pad_byte] is the ASCII '=' character used as padding. *)
let pad_byte : byte = U8.uint_to_t 0x3D

(** [is_pad b] is true when byte [b] is '='. *)
let is_pad (b: byte) : bool = U8.v b = 0x3D

(** Alphabet roundtrip *)

(** Base32 character roundtrip: encode then decode returns the original 5-bit
    value. *)
let lemma_b32_char_roundtrip () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 31}). base32_char_to_val (b32_val i) == Some i))
  = ()

(** [b32_val i] is never the pad character '=' (0x3D). *)
let lemma_b32_val_not_pad () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 31}). not (is_pad (b32_val i))))
  = ()

(** [b32_val i] always produces a valid base32 character. *)
let lemma_b32_val_is_char () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 31}). is_base32_char (b32_val i)))
  = ()

(** encode_base32 — explicit cons, no [@] *)

(** [encode_base32] encodes bytes to RFC 4648 §6 base32 characters.
    All cases use explicit cons (no [@]) so the SMT can see the list
    structure directly.
    (* Partial blocks (1-4 bytes) duplicate the bit-slicing formulas
       from the 5-byte full block.  Kept inline because factoring
       into a helper would introduce a list-append span that SMT
       cannot reason through. *)
    @param bs Input byte list.
    @returns List of base32 character bytes with = padding. *)
let rec encode_base32 (bs: list byte) : Tot (list byte) (decreases bs) =
  match bs with
  | [] -> []
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in
    let v2 = U8.v b2 in let v3 = U8.v b3 in let v4 = U8.v b4 in
    b32_val (v0 / 8) ::
    b32_val ((v0 % 8) * 4 + v1 / 64) ::
    b32_val ((v1 / 2) % 32) ::
    b32_val ((v1 % 2) * 16 + v2 / 16) ::
    b32_val ((v2 % 16) * 2 + v3 / 128) ::
    b32_val ((v3 / 4) % 32) ::
    b32_val ((v3 % 4) * 8 + v4 / 32) ::
    b32_val (v4 % 32) ::
    encode_base32 rest
  | [b0] ->
    let v0 = U8.v b0 in
    b32_val (v0 / 8) :: b32_val ((v0 % 8) * 4) ::
    pad_byte :: pad_byte :: pad_byte :: pad_byte :: pad_byte :: pad_byte :: []
  | [b0; b1] ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in
    b32_val (v0 / 8) :: b32_val ((v0 % 8) * 4 + v1 / 64) ::
    b32_val ((v1 / 2) % 32) :: b32_val ((v1 % 2) * 16) ::
    pad_byte :: pad_byte :: pad_byte :: pad_byte :: []
  | [b0; b1; b2] ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in let v2 = U8.v b2 in
    b32_val (v0 / 8) :: b32_val ((v0 % 8) * 4 + v1 / 64) ::
    b32_val ((v1 / 2) % 32) :: b32_val ((v1 % 2) * 16 + v2 / 16) ::
    b32_val ((v2 % 16) * 2) ::
    pad_byte :: pad_byte :: pad_byte :: []
  | [b0; b1; b2; b3] ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in
    let v2 = U8.v b2 in let v3 = U8.v b3 in
    b32_val (v0 / 8) :: b32_val ((v0 % 8) * 4 + v1 / 64) ::
    b32_val ((v1 / 2) % 32) :: b32_val ((v1 % 2) * 16 + v2 / 16) ::
    b32_val ((v2 % 16) * 2 + v3 / 128) ::
    b32_val ((v3 / 4) % 32) :: b32_val ((v3 % 4) * 8) ::
    pad_byte :: []

(** Byte extraction lemmas *)

(** Byte 0 extraction: v0 = (v0/8)*8 + ((v0%8)*4 + v1/64)/4. *)
let lemma_b32_byte0 (v0 v1: int) : Lemma
  (requires 0 <= v0 /\ v0 < 256 /\ 0 <= v1 /\ v1 < 256)
  (ensures (v0 / 8) * 8 + ((v0 % 8) * 4 + v1 / 64) / 4 == v0)
  = lemma_div_mod v0 8;
    small_div (v1 / 64) 4

(** Byte 1 extraction: v1 = (c1%4)*64 + c2*2 + c3/16 where
    c1 = (v0%8)*4 + v1/64, c2 = (v1/2)%32, c3 = (v1%2)*16 + v2/16. *)
let lemma_b32_byte1 (v0 v1 v2: int) : Lemma
  (requires 0 <= v0 /\ v0 < 256 /\ 0 <= v1 /\ v1 < 256 /\ 0 <= v2 /\ v2 < 256)
  (ensures
    (let c1 = (v0 % 8) * 4 + v1 / 64 in
     let c2 = (v1 / 2) % 32 in
     let c3 = (v1 % 2) * 16 + v2 / 16 in
     (c1 % 4) * 64 + c2 * 2 + c3 / 16 == v1))
  = lemma_div_mod v1 64;
    small_div (v2 / 16) 16;
    lemma_mod_plus_distr_l ((v0 % 8) * 4) (v1 / 64) 4

(** Byte 2 extraction: v2 = (c3%16)*16 + c4/2 where
    c3 = (v1%2)*16 + v2/16, c4 = (v2%16)*2 + v3/128. *)
let lemma_b32_byte2 (v1 v2 v3: int) : Lemma
  (requires 0 <= v1 /\ v1 < 256 /\ 0 <= v2 /\ v2 < 256 /\ 0 <= v3 /\ v3 < 256)
  (ensures
    (let c3 = (v1 % 2) * 16 + v2 / 16 in
     let c4 = (v2 % 16) * 2 + v3 / 128 in
     (c3 % 16) * 16 + c4 / 2 == v2))
  = lemma_div_mod v2 16;
    small_div (v3 / 128) 2;
    lemma_mod_plus_distr_l ((v1 % 2) * 16) (v2 / 16) 16

(** Byte 3 extraction: v3 = (c4%2)*128 + c5*4 + c6/8 where
    c4 = (v2%16)*2 + v3/128, c5 = (v3/4)%32, c6 = (v3%4)*8 + v4/32. *)
let lemma_b32_byte3 (v2 v3 v4: int) : Lemma
  (requires 0 <= v2 /\ v2 < 256 /\ 0 <= v3 /\ v3 < 256 /\ 0 <= v4 /\ v4 < 256)
  (ensures
    (let c4 = (v2 % 16) * 2 + v3 / 128 in
     let c5 = (v3 / 4) % 32 in
     let c6 = (v3 % 4) * 8 + v4 / 32 in
     (c4 % 2) * 128 + c5 * 4 + c6 / 8 == v3))
  = lemma_div_mod v3 128;
    lemma_div_mod v3 4;
    small_div (v4 / 32) 8;
    lemma_mod_plus_distr_l ((v2 % 16) * 2) (v3 / 128) 2

(** Byte 4 extraction: v4 = (c6%8)*32 + c7 where
    c6 = (v3%4)*8 + v4/32, c7 = v4%32. *)
let lemma_b32_byte4 (v3 v4: int) : Lemma
  (requires 0 <= v3 /\ v3 < 256 /\ 0 <= v4 /\ v4 < 256)
  (ensures
    (let c6 = (v3 % 4) * 8 + v4 / 32 in
     let c7 = v4 % 32 in
     (c6 % 8) * 32 + c7 == v4))
  = lemma_div_mod v4 32;
    lemma_mod_plus_distr_l ((v3 % 4) * 8) (v4 / 32) 8

(** decode_base32 — non-recursive group decoder + recursive loop, no [@] *)

(** [decode_base32_group] decodes one 8-character base32 group.
    Handles all 5 padding cases (pad_count = 0, 1, 3, 4, 6).
    Non-recursive — no [decreases] clause needed.
    Nested match depth is 3; intentional trade-off to keep
    all validation in one place vs introducing per-pad-count helpers.
    @param group A list of exactly 8 bytes (the 8 base32 chars).
    @returns [Some bytes] (1-5 decoded bytes) on success, [None] on invalid input. *)
let decode_base32_group (group: list byte) : option (list byte) =
  match group with
  | [c0; c1; c2; c3; c4; c5; c6; c7] ->
    if is_pad c0 || is_pad c1 then None
    else if not (is_base32_char c0 && is_base32_char c1) then None
    else
    let pad_count =
        (if is_pad c7 then 1 else 0) + (if is_pad c6 then 1 else 0) +
        (if is_pad c5 then 1 else 0) + (if is_pad c4 then 1 else 0) +
        (if is_pad c3 then 1 else 0) + (if is_pad c2 then 1 else 0) in
    (match base32_char_to_val c0, base32_char_to_val c1 with
     | Some v0, Some v1 ->
       if pad_count = 0 then
         (match base32_char_to_val c2, base32_char_to_val c3,
                base32_char_to_val c4, base32_char_to_val c5,
                base32_char_to_val c6, base32_char_to_val c7 with
          | Some v2, Some v3, Some v4, Some v5, Some v6, Some v7 ->
            Some [U8.uint_to_t (nat_of_int (v0 * 8 + v1 / 4));
                 U8.uint_to_t (nat_of_int ((v1 % 4) * 64 + v2 * 2 + v3 / 16));
                 U8.uint_to_t (nat_of_int ((v3 % 16) * 16 + v4 / 2));
                 U8.uint_to_t (nat_of_int ((v4 % 2) * 128 + v5 * 4 + v6 / 8));
                 U8.uint_to_t (nat_of_int ((v6 % 8) * 32 + v7))]
          | _ -> None)
       else if pad_count = 1 then
         (match base32_char_to_val c2, base32_char_to_val c3,
                base32_char_to_val c4, base32_char_to_val c5,
                base32_char_to_val c6 with
          | Some v2, Some v3, Some v4, Some v5, Some v6 ->
            if not (is_pad c7) then None else
            Some [U8.uint_to_t (nat_of_int (v0 * 8 + v1 / 4));
                 U8.uint_to_t (nat_of_int ((v1 % 4) * 64 + v2 * 2 + v3 / 16));
                 U8.uint_to_t (nat_of_int ((v3 % 16) * 16 + v4 / 2));
                 U8.uint_to_t (nat_of_int ((v4 % 2) * 128 + v5 * 4 + v6 / 8))]
          | _ -> None)
       else if pad_count = 3 then
         (match base32_char_to_val c2, base32_char_to_val c3,
                base32_char_to_val c4 with
          | Some v2, Some v3, Some v4 ->
            if not (is_pad c5 && is_pad c6 && is_pad c7) then None else
            Some [U8.uint_to_t (nat_of_int (v0 * 8 + v1 / 4));
                 U8.uint_to_t (nat_of_int ((v1 % 4) * 64 + v2 * 2 + v3 / 16));
                 U8.uint_to_t (nat_of_int ((v3 % 16) * 16 + v4 / 2))]
          | _ -> None)
       else if pad_count = 4 then
         (match base32_char_to_val c2, base32_char_to_val c3 with
          | Some v2, Some v3 ->
            if not (is_pad c4 && is_pad c5 && is_pad c6 && is_pad c7) then None else
            Some [U8.uint_to_t (nat_of_int (v0 * 8 + v1 / 4));
                 U8.uint_to_t (nat_of_int ((v1 % 4) * 64 + v2 * 2 + v3 / 16))]
          | _ -> None)
       else if pad_count = 6 then
         (if not (is_pad c2 && is_pad c3 && is_pad c4 && is_pad c5 && is_pad c6 && is_pad c7) then None else
          Some [U8.uint_to_t (nat_of_int (v0 * 8 + v1 / 4))])
       else None
     | _ -> None)
  | _ -> None

(** [decode_base32] parses groups of 8 base32 chars with = padding.
    Uses explicit cons pattern matching (no [@]) so the SMT can see
    through the list structure directly.
    @param bs Input base32 character list.
    @returns [Some bytes] on success, [None] on invalid input. *)
let rec decode_base32 (bs: list byte) : Tot (option (list byte)) (decreases (L.length bs)) =
  match bs with
  | [] -> Some []
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest ->
    (match decode_base32_group [c0; c1; c2; c3; c4; c5; c6; c7] with
     | Some bytes ->
       (match decode_base32 rest with
        | Some tl ->
          (match bytes with
           | [b0] -> Some (b0 :: tl)
           | [b0; b1] -> Some (b0 :: b1 :: tl)
           | [b0; b1; b2] -> Some (b0 :: b1 :: b2 :: tl)
           | [b0; b1; b2; b3] -> Some (b0 :: b1 :: b2 :: b3 :: tl)
           | [b0; b1; b2; b3; b4] -> Some (b0 :: b1 :: b2 :: b3 :: b4 :: tl)
           (* decode_base32_group never returns other lengths;
              this branch is provably dead, kept for match exhaustiveness *)
           | _ -> None)
        | None -> None)
     | None -> None)
  | _ -> None

(** Proof lemmas *)

(** [decode_base32_group] directly on the 8 encoded chars returns the
    5 original bytes. *)
let lemma_decode_base32_group_quintet (b0 b1 b2 b3 b4: byte) : Lemma
  (let v0 = U8.v b0 in let v1 = U8.v b1 in
   let v2 = U8.v b2 in let v3 = U8.v b3 in let v4 = U8.v b4 in
   decode_base32_group [b32_val (v0 / 8);
                        b32_val ((v0 % 8) * 4 + v1 / 64);
                        b32_val ((v1 / 2) % 32);
                        b32_val ((v1 % 2) * 16 + v2 / 16);
                        b32_val ((v2 % 16) * 2 + v3 / 128);
                        b32_val ((v3 / 4) % 32);
                        b32_val ((v3 % 4) * 8 + v4 / 32);
                        b32_val (v4 % 32)]
   == Some [b0; b1; b2; b3; b4])
  = lemma_b32_char_roundtrip ();
    lemma_b32_val_not_pad ();
    lemma_b32_val_is_char ();
    lemma_b32_byte0 (U8.v b0) (U8.v b1);
    lemma_b32_byte1 (U8.v b0) (U8.v b1) (U8.v b2);
    lemma_b32_byte2 (U8.v b1) (U8.v b2) (U8.v b3);
    lemma_b32_byte3 (U8.v b2) (U8.v b3) (U8.v b4);
    lemma_b32_byte4 (U8.v b3) (U8.v b4)

(** Per-block roundtrip lemmas *)

(** 5-byte block roundtrip. *)
let lemma_base32_quintet (b0 b1 b2 b3 b4: byte) : Lemma
  (ensures decode_base32 (encode_base32 [b0; b1; b2; b3; b4]) == Some [b0; b1; b2; b3; b4])
  = lemma_decode_base32_group_quintet b0 b1 b2 b3 b4

(** 4-byte block (with one pad) roundtrip.
    [v4=0]: passes zero for the absent 5th byte — the byte-extraction
    lemma [lemma_b32_byte3] handles v4=0 gracefully since the arithmetic
    identities hold for all byte values including zero.
    @param b0 b1 b2 b3 The 4 bytes to encode. *)
let lemma_base32_quad (b0 b1 b2 b3: byte) : Lemma
  (ensures decode_base32 (encode_base32 [b0; b1; b2; b3]) == Some [b0; b1; b2; b3])
  = lemma_b32_char_roundtrip ();
    lemma_b32_val_not_pad ();
    lemma_b32_val_is_char ();
    lemma_b32_byte0 (U8.v b0) (U8.v b1);
    lemma_b32_byte1 (U8.v b0) (U8.v b1) (U8.v b2);
    lemma_b32_byte2 (U8.v b1) (U8.v b2) (U8.v b3);
    lemma_b32_byte3 (U8.v b2) (U8.v b3) 0

(** 3-byte block (with three pads) roundtrip.
    [v3=v4=0]: see [lemma_base32_quad]. *)
let lemma_base32_triple (b0 b1 b2: byte) : Lemma
  (ensures decode_base32 (encode_base32 [b0; b1; b2]) == Some [b0; b1; b2])
  = lemma_b32_char_roundtrip ();
    lemma_b32_val_not_pad ();
    lemma_b32_val_is_char ();
    lemma_b32_byte0 (U8.v b0) (U8.v b1);
    lemma_b32_byte1 (U8.v b0) (U8.v b1) (U8.v b2);
    lemma_b32_byte2 (U8.v b1) (U8.v b2) 0

(** 2-byte block (with four pads) roundtrip.
    [v2=v3=v4=0]: see [lemma_base32_quad]. *)
let lemma_base32_pair (b0 b1: byte) : Lemma
  (ensures decode_base32 (encode_base32 [b0; b1]) == Some [b0; b1])
  = lemma_b32_char_roundtrip ();
    lemma_b32_val_not_pad ();
    lemma_b32_val_is_char ();
    lemma_b32_byte0 (U8.v b0) (U8.v b1);
    lemma_b32_byte1 (U8.v b0) (U8.v b1) 0

(** 1-byte block (with six pads) roundtrip.
    [v1=v2=v3=v4=0]: see [lemma_base32_quad]. *)
let lemma_base32_single (b0: byte) : Lemma
  (ensures decode_base32 (encode_base32 [b0]) == Some [b0])
  = lemma_b32_char_roundtrip ();
    lemma_b32_val_not_pad ();
    lemma_b32_val_is_char ();
    lemma_b32_byte0 (U8.v b0) 0

(** Full roundtrip by induction.

    Each step calls [lemma_decode_base32_group_quintet] for the group
    content and the IH for the tail. Because both encode and decode use
    explicit cons (no [@]), the SMT can see through the list structure
    and chain the group result with the recursive result directly. *)
#push-options "--z3rlimit 30"
let rec lemma_base32_roundtrip (bs: list byte) : Lemma
  (ensures decode_base32 (encode_base32 bs) == Some bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | [b0] -> lemma_base32_single b0
    | [b0; b1] -> lemma_base32_pair b0 b1
    | [b0; b1; b2] -> lemma_base32_triple b0 b1 b2
    | [b0; b1; b2; b3] -> lemma_base32_quad b0 b1 b2 b3
    | b0 :: b1 :: b2 :: b3 :: b4 :: tl ->
      lemma_decode_base32_group_quintet b0 b1 b2 b3 b4;
      lemma_base32_roundtrip tl
#pop-options

(** Concrete test vectors — RFC 4648 §10 *)

(** "" -> "". *)
let lemma_base32_empty () : Lemma
  (ensures encode_base32 [] == [] /\ decode_base32 [] == Some [])
  = ()

(** "f" -> "MY======". *)
let lemma_base32_f () : Lemma
  (ensures encode_base32 [0x66uy] == [0x4Duy; 0x59uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy])
  = lemma_b32_char_roundtrip ()

(** "fo" -> "MZXQ====". *)
let lemma_base32_fo () : Lemma
  (ensures encode_base32 [0x66uy; 0x6Fuy] == [0x4Duy; 0x5Auy; 0x58uy; 0x51uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy])
  = lemma_b32_char_roundtrip ()

(** "foo" -> "MZXW6===". *)
let lemma_base32_foo () : Lemma
  (ensures encode_base32 [0x66uy; 0x6Fuy; 0x6Fuy]
        == [0x4Duy; 0x5Auy; 0x58uy; 0x57uy; 0x36uy; 0x3Duy; 0x3Duy; 0x3Duy])
  = lemma_b32_char_roundtrip ()

(** "foob" -> "MZXW6YQ=". *)
let lemma_base32_foob () : Lemma
  (ensures encode_base32 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy]
        == [0x4Duy; 0x5Auy; 0x58uy; 0x57uy; 0x36uy; 0x59uy; 0x51uy; 0x3Duy])
  = lemma_b32_char_roundtrip ()

(** "fooba" -> "MZXW6YTB". *)
let lemma_base32_fooba () : Lemma
  (ensures encode_base32 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy; 0x61uy]
        == [0x4Duy; 0x5Auy; 0x58uy; 0x57uy; 0x36uy; 0x59uy; 0x54uy; 0x42uy])
  = lemma_b32_char_roundtrip ()

(** "foobar" -> "MZXW6YTBOI======". *)
let lemma_base32_foobar () : Lemma
  (ensures encode_base32 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy; 0x61uy; 0x72uy]
        == [0x4Duy; 0x5Auy; 0x58uy; 0x57uy; 0x36uy; 0x59uy; 0x54uy; 0x42uy;
            0x4Fuy; 0x49uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy])
  = lemma_b32_char_roundtrip ()

(** Decode "MY======" -> Some [0x66]. *)
let lemma_base32_decode_f () : Lemma
  (ensures decode_base32 [0x4Duy; 0x59uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy] == Some [0x66uy])
  = lemma_b32_char_roundtrip ()

(** Decode "MZXW6YTB" -> Some [0x66; 0x6F; 0x6F; 0x62; 0x61]. *)
let lemma_base32_decode_fooba () : Lemma
  (ensures decode_base32 [0x4Duy; 0x5Auy; 0x58uy; 0x57uy; 0x36uy; 0x59uy; 0x54uy; 0x42uy]
        == Some [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy; 0x61uy])
  = lemma_b32_char_roundtrip ()

(** Error: invalid char '1' returns None. *)
let lemma_base32_decode_invalid_char () : Lemma
  (ensures decode_base32 [0x31uy; 0x59uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy] == None)
  = ()

(** Error: pad in first position returns None. *)
let lemma_base32_decode_pad_first () : Lemma
  (ensures decode_base32 [0x3Duy; 0x59uy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy; 0x3Duy] == None)
  = ()

(** Error: wrong-length input returns None. *)
let lemma_base32_decode_bad_length () : Lemma
  (ensures decode_base32 [0x4Duy; 0x59uy] == None)
  = ()

(** Roundtrip on concrete values. *)
let lemma_base32_roundtrip_concrete () : Lemma
  (ensures decode_base32 (encode_base32 [0x66uy; 0x6Fuy; 0x6Fuy])
        == Some [0x66uy; 0x6Fuy; 0x6Fuy])
  = lemma_base32_roundtrip [0x66uy; 0x6Fuy; 0x6Fuy]
