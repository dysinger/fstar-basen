(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)


(**
Data.BaseN.Base64 — RFC 4648 §4 Base64 Encoding

ZERO admits. ZERO --admit_smt_queries. 100% lemmas proven.

Architecture:
- encode_base64: all cases use explicit cons (no @). Direct bit-slicing
  formulas — structural inverses of decode_base64. No Horner-form triple
  arithmetic.
- decode_base64: explicit cons pattern matching (no @) on 4-char groups
  with = padding handling.
- Helper lemmas (lemma_b64_byte0, lemma_b64_byte1, lemma_b64_byte2) prove
  extraction identities.
- lemma_base64_roundtrip: induction with explicit per-block lemmas.
  The cons-based approach eliminates all @ from encode/decode, letting
  the SMT see through the list structure directly.

@header Data.BaseN.Base64
*)
module Data.BaseN.Base64


open Data.Codec.Types
open FStar.UInt8
open FStar.List.Tot
open FStar.Math.Lemmas


module U8 = FStar.UInt8
module L = FStar.List.Tot


(** Base64 alphabet *)


(** [b64_val i] maps a 6-bit value to its RFC 4648 §4 base64 character.
    @param i Integer in [0, 63]. *)
let b64_val (i: int{0 <= i /\ i <= 63}) : Tot byte =
  let u = U8.uint_to_t in
  if i <= 25 then u (0x41 + i)
  else if i <= 51 then u (0x61 + i - 26)
  else if i <= 61 then u (0x30 + i - 52)
  else if i = 62 then u 0x2B
  else u 0x2F


(** [base64_char_to_val b] converts a base64 character to its 6-bit value.
    @param b Byte representing a base64 character.
    @returns [Some i] with [0 <= i <= 63], or [None] if [b] is not base64. *)
let base64_char_to_val (b: byte) : option int =
  let v = U8.v b in
  if 0x41 <= v && v <= 0x5A then Some (v - 0x41)
  else if 0x61 <= v && v <= 0x7A then Some (v - 0x61 + 26)
  else if 0x30 <= v && v <= 0x39 then Some (v - 0x30 + 52)
  else if v = 0x2B then Some 62
  else if v = 0x2F then Some 63
  else None


(** [is_base64_char b] is true when byte [b] is a valid RFC 4648 §4 base64
    character (A-Z, a-z, 0-9, +, /). Padding (=) is NOT a base64 char. *)
let is_base64_char (b: byte) : bool =
  let v = U8.v b in
  (0x41 <= v && v <= 0x5A) || (0x61 <= v && v <= 0x7A) ||
  (0x30 <= v && v <= 0x39) || v = 0x2B || v = 0x2F


(** [pad_byte] is the ASCII '=' character used as padding. *)
let pad_byte : byte = U8.uint_to_t 0x3D


(** [is_pad b] is true when byte [b] is '='. *)
let is_pad (b: byte) : bool = U8.v b = 0x3D


(** Alphabet roundtrip *)


(** Base64 character roundtrip: encode then decode returns the original 6-bit
    value. *)
let lemma_b64_char_roundtrip () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 63}). base64_char_to_val (b64_val i) == Some i))
  = ()


(** [b64_val i] is never the pad character '='. *)
let lemma_b64_val_not_pad () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 63}). not (is_pad (b64_val i))))
  = ()


(** [b64_val i] always produces a valid base64 character. *)
let lemma_b64_val_is_char () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 63}). is_base64_char (b64_val i)))
  = ()


(** encode_base64 — explicit cons, no [@], direct formulas *)


(** [encode_base64] encodes bytes to RFC 4648 §4 base64 characters.
    All cases use explicit cons (no [@]) and direct bit-slicing formulas
    that are structural inverses of [decode_base64].
    @param bs Input byte list.
    @returns List of base64 character bytes with = padding. *)
let rec encode_base64 (bs: list byte) : Tot (list byte) (decreases bs) =
  match bs with
  | [] -> []
  | b0 :: b1 :: b2 :: rest ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in let v2 = U8.v b2 in
    b64_val (v0 / 4) ::
    b64_val ((v0 % 4) * 16 + v1 / 16) ::
    b64_val ((v1 % 16) * 4 + v2 / 64) ::
    b64_val (v2 % 64) ::
    encode_base64 rest
  | [b0] ->
    let v0 = U8.v b0 in
    b64_val (v0 / 4) :: b64_val ((v0 % 4) * 16) :: pad_byte :: pad_byte :: []
  | [b0; b1] ->
    let v0 = U8.v b0 in let v1 = U8.v b1 in
    b64_val (v0 / 4) :: b64_val ((v0 % 4) * 16 + v1 / 16) ::
    b64_val ((v1 % 16) * 4) :: pad_byte :: []


(** Byte extraction lemmas *)


(** Byte 0 extraction: v0 = (v0/4)*4 + ((v0%4)*16 + v1/16)/16. *)
let lemma_b64_byte0 (v0 v1: int) : Lemma
  (requires 0 <= v0 /\ v0 < 256 /\ 0 <= v1 /\ v1 < 256)
  (ensures (v0 / 4) * 4 + ((v0 % 4) * 16 + v1 / 16) / 16 == v0)
  = lemma_div_mod v0 4;
    small_div (v1 / 16) 16


(** Byte 1 extraction for the 2-byte tail:
    v1 = (c1%16)*16 + c2/4 where
    c1 = (v0%4)*16 + v1/16, c2 = (v1%16)*4. *)
let lemma_b64_byte1 (v0 v1: int) : Lemma
  (requires 0 <= v0 /\ v0 < 256 /\ 0 <= v1 /\ v1 < 256)
  (ensures
    (let c1 = (v0 % 4) * 16 + v1 / 16 in
     let c2 = (v1 % 16) * 4 in
     (c1 % 16) * 16 + c2 / 4 == v1))
  = lemma_div_mod v1 16;
    cancel_mul_div (v1 % 16) 4


(** Byte 2 extraction for the 3-byte case:
    v2 = (c2%4)*64 + c3 where
    c2 = (v1%16)*4 + v2/64, c3 = v2%64. *)
let lemma_b64_byte2 (v1 v2: int) : Lemma
  (requires 0 <= v1 /\ v1 < 256 /\ 0 <= v2 /\ v2 < 256)
  (ensures
    (let c2 = (v1 % 16) * 4 + v2 / 64 in
     let c3 = v2 % 64 in
     (c2 % 4) * 64 + c3 == v2))
  = lemma_div_mod v2 64;
    lemma_mod_plus_distr_l ((v1 % 16) * 4) (v2 / 64) 4


(** decode_base64 — explicit cons, no [@] *)


(** [decode_base64] parses groups of 4 base64 chars with = padding.
    Uses explicit cons pattern matching (no [@]).
    @param bs Input base64 character list.
    @returns [Some bytes] on success, [None] on invalid input. *)
let rec decode_base64 (bs: list byte) : Tot (option (list byte)) (decreases (L.length bs)) =
  match bs with
  | [] -> Some []
  | c0 :: c1 :: c2 :: c3 :: rest ->
    let pad_count : int = (if is_pad c3 then 1 else 0) + (if is_pad c2 then 1 else 0) in
    if is_pad c0 || is_pad c1 then None
    else if not (is_base64_char c0 && is_base64_char c1) then None
    else
      (match base64_char_to_val c0, base64_char_to_val c1 with
       | Some v0, Some v1 ->
         let b0 = U8.uint_to_t (nat_of_int (v0 * 4 + v1 / 16)) in
         if pad_count >= 2 then
           (match decode_base64 rest with
            | Some tl -> Some (b0 :: tl)
            | None -> None)
         else if not (is_base64_char c2) || is_pad c2 then None
         else
           (match base64_char_to_val c2 with
            | Some v2 ->
              let b1 = U8.uint_to_t (nat_of_int ((v1 % 16) * 16 + v2 / 4)) in
              if pad_count = 1 then
                (match decode_base64 rest with
                 | Some tl -> Some (b0 :: b1 :: tl)
                 | None -> None)
              else if not (is_base64_char c3) || is_pad c3 then None
              else
                (match base64_char_to_val c3 with
                 | Some v3 ->
                   let b2 = U8.uint_to_t (nat_of_int ((v2 % 4) * 64 + v3)) in
                   (match decode_base64 rest with
                    | Some tl -> Some (b0 :: b1 :: b2 :: tl)
                    | None -> None)
                 | None -> None)
            | None -> None)
       | _ -> None)
  | _ -> None


(** Per-block roundtrip lemmas *)


(** 1-byte block (with two pads) roundtrip. *)
let lemma_base64_single (b0: byte) : Lemma
  (ensures decode_base64 (encode_base64 [b0]) == Some [b0])
  = lemma_b64_char_roundtrip ();
    lemma_b64_val_not_pad ();
    lemma_b64_val_is_char ();
    lemma_b64_byte0 (U8.v b0) 0


(** 2-byte block (with one pad) roundtrip. *)
let lemma_base64_pair (b0 b1: byte) : Lemma
  (ensures decode_base64 (encode_base64 [b0; b1]) == Some [b0; b1])
  = lemma_b64_char_roundtrip ();
    lemma_b64_val_not_pad ();
    lemma_b64_val_is_char ();
    lemma_b64_byte0 (U8.v b0) (U8.v b1);
    lemma_b64_byte1 (U8.v b0) (U8.v b1)


(** 3-byte block roundtrip.

    The encode uses direct formulas:
      c0 = v0/4, c1 = (v0%4)*16 + v1/16,
      c2 = (v1%16)*4 + v2/64, c3 = v2%64
    The decode uses the structural inverses. The byte extraction lemmas
    [lemma_b64_byte0], [lemma_b64_byte1], [lemma_b64_byte2] prove the
    identities directly. *)
#push-options "--z3rlimit 20"
let lemma_base64_triple (b0 b1 b2: byte) : Lemma
  (ensures decode_base64 (encode_base64 [b0; b1; b2]) == Some [b0; b1; b2])
  = lemma_b64_char_roundtrip ();
    lemma_b64_val_not_pad ();
    lemma_b64_val_is_char ();
    lemma_b64_byte0 (U8.v b0) (U8.v b1);
    lemma_b64_byte1 (U8.v b0) (U8.v b1);
    lemma_b64_byte2 (U8.v b1) (U8.v b2)
#pop-options


(** Full roundtrip by induction.

    Each step calls the appropriate per-block lemma for the content
    and the IH for the tail. Because both encode and decode use explicit
    cons (no [@]), the SMT can see through the list structure and chain
    the results directly. *)
#push-options "--z3rlimit 30"
let rec lemma_base64_roundtrip (bs: list byte) : Lemma
  (ensures decode_base64 (encode_base64 bs) == Some bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | [b0] -> lemma_base64_single b0
    | [b0; b1] ->
      lemma_base64_pair b0 b1
    | b0 :: b1 :: b2 :: tl ->
      lemma_base64_triple b0 b1 b2;
      lemma_base64_roundtrip tl
#pop-options


(** Concrete test vectors — RFC 4648 §10 *)


(** "" -> "". *)
let lemma_base64_empty () : Lemma
  (ensures encode_base64 [] == [] /\ decode_base64 [] == Some [])
  = ()


(** "f" -> "Zg==". *)
let lemma_base64_f () : Lemma
  (ensures encode_base64 [0x66uy] == [0x5Auy; 0x67uy; 0x3Duy; 0x3Duy])
  = lemma_b64_char_roundtrip ()


(** "fo" -> "Zm8=". *)
let lemma_base64_fo () : Lemma
  (ensures encode_base64 [0x66uy; 0x6Fuy] == [0x5Auy; 0x6Duy; 0x38uy; 0x3Duy])
  = lemma_b64_char_roundtrip ()


(** "foo" -> "Zm9v". *)
let lemma_base64_foo () : Lemma
  (ensures encode_base64 [0x66uy; 0x6Fuy; 0x6Fuy]
        == [0x5Auy; 0x6Duy; 0x39uy; 0x76uy])
  = lemma_b64_char_roundtrip ()


(** "foob" -> "Zm9vYg==". *)
let lemma_base64_foob () : Lemma
  (ensures encode_base64 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy]
        == [0x5Auy; 0x6Duy; 0x39uy; 0x76uy; 0x59uy; 0x67uy; 0x3Duy; 0x3Duy])
  = lemma_b64_char_roundtrip ()


(** "fooba" -> "Zm9vYmE=". *)
let lemma_base64_fooba () : Lemma
  (ensures encode_base64 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy; 0x61uy]
        == [0x5Auy; 0x6Duy; 0x39uy; 0x76uy; 0x59uy; 0x6Duy; 0x45uy; 0x3Duy])
  = lemma_b64_char_roundtrip ()


(** "foobar" -> "Zm9vYmFy". *)
let lemma_base64_foobar () : Lemma
  (ensures encode_base64 [0x66uy; 0x6Fuy; 0x6Fuy; 0x62uy; 0x61uy; 0x72uy]
        == [0x5Auy; 0x6Duy; 0x39uy; 0x76uy; 0x59uy; 0x6Duy; 0x46uy; 0x79uy])
  = lemma_b64_char_roundtrip ()


(** Decode "Zg==" -> "f". *)
let lemma_base64_decode_f () : Lemma
  (ensures decode_base64 [0x5Auy; 0x67uy; 0x3Duy; 0x3Duy] == Some [0x66uy])
  = lemma_b64_char_roundtrip ()


(** Decode "Zm9v" -> "foo". *)
let lemma_base64_decode_foo () : Lemma
  (ensures decode_base64 [0x5Auy; 0x6Duy; 0x39uy; 0x76uy] == Some [0x66uy; 0x6Fuy; 0x6Fuy])
  = lemma_b64_char_roundtrip ()


(** Error: invalid char '!' returns None. *)
let lemma_base64_decode_invalid_char () : Lemma
  (ensures decode_base64 [0x21uy; 0x67uy; 0x3Duy; 0x3Duy] == None)
  = ()


(** Error: pad in first position returns None. *)
let lemma_base64_decode_pad_first () : Lemma
  (ensures decode_base64 [0x3Duy; 0x67uy; 0x3Duy; 0x3Duy] == None)
  = ()


(** Error: wrong-length input returns None. *)
let lemma_base64_decode_bad_length () : Lemma
  (ensures decode_base64 [0x5Auy; 0x67uy] == None)
  = ()


(** Roundtrip on concrete values. *)
let lemma_base64_roundtrip_concrete () : Lemma
  (ensures decode_base64 (encode_base64 [0x4Duy; 0x61uy; 0x6Euy])
        == Some [0x4Duy; 0x61uy; 0x6Euy])
  = lemma_base64_roundtrip [0x4Duy; 0x61uy; 0x6Euy]
