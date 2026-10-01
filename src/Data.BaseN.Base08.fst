(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.BaseN.Base08 — Octal Byte Encoding (3 digits per byte)

Built directly on UInt8 arithmetic with list induction.
ZERO admits. ZERO --admit_smt_queries. 100% lemmas proven.

Architecture:
- is_octal_digit, octal_digit_to_int, int_to_octal_digit: char ↔ value
- encode_base08: each byte → 3 octal digits (zero-padded to 3)
- decode_base08: parse triples of octal digits → bytes
- lemma_base08_roundtrip: structural induction on input list

@header Data.BaseN.Base08
*)
module Data.BaseN.Base08

open FStar.UInt8
open FStar.List.Tot

module U8 = FStar.UInt8
module L = FStar.List.Tot

(** Character predicates *)

(** [is_octal_digit b] is true when byte [b] is '0'..'7'. *)
let is_octal_digit (b: UInt8.t) : bool =
  let v = U8.v b in 0x30 <= v && v <= 0x37

(** [octal_digit_to_int b] converts '0'..'7' to 0..7.
    @param b Byte representing an octal digit.
    @returns Integer in [0, 7]. *)
let octal_digit_to_int (b: UInt8.t{is_octal_digit b}) : n:int{0 <= n /\ n <= 7} =
  U8.v b - 0x30

(** [int_to_octal_digit n] converts 0..7 to '0'..'7'.
    @param n Integer in [0, 7]. *)
let int_to_octal_digit (n: int{0 <= n /\ n <= 7}) : UInt8.t =
  U8.uint_to_t (0x30 + n)

(** encode_base08 / decode_base08 *)

(** [encode_base08] encodes each byte as three zero-padded octal digits.
    Always produces exactly 3 characters per byte.
    @param bs Input byte list.
    @returns List of octal character bytes. *)
let encode_base08 (bs: list UInt8.t) : list UInt8.t =
  L.flatten (L.map (fun (b: UInt8.t) ->
    let v = U8.v b in
    [int_to_octal_digit (v / 64);
     int_to_octal_digit ((v / 8) % 8);
     int_to_octal_digit (v % 8)]
  ) bs)

(** [decode_base08] parses groups of 3 octal digits into bytes.
    Three octal digits represent 0..511, exceeding the byte range
    0..255, so an explicit [n > 255] overflow check is required.
    (Contrast with Base16 where two hex digits always produce 0..255.)
    @param bs Input octal character list.
    @returns [Some bytes] on success, [None] on non-multiple-of-3 or non-octal char. *)
let rec decode_base08 (bs: list UInt8.t) : Tot (option (list UInt8.t)) (decreases (L.length bs)) =
  match bs with
  | [] -> Some []
  | d0 :: d1 :: d2 :: rest ->
    if is_octal_digit d0 && is_octal_digit d1 && is_octal_digit d2 then
      let n = octal_digit_to_int d0 * 64 +
              octal_digit_to_int d1 * 8 +
              octal_digit_to_int d2 in
      if n > 255 then None else
      (match decode_base08 rest with
       | Some tl -> Some (U8.uint_to_t n :: tl)
       | None -> None)
    else None
  | _ -> None

(** Digit conversion lemmas *)

(** Each octal digit 0-7 maps to/from a valid character losslessly. *)
let lemma_octal_digit_roundtrip () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 7}).
            octal_digit_to_int (int_to_octal_digit i) == i /\
            is_octal_digit (int_to_octal_digit i)))
  = ()

(** [encode_base08] of a single byte produces exactly 3 valid octal digits. *)
let lemma_encode_base08_single (b: UInt8.t) : Lemma
  (let bs = encode_base08 [b] in
   L.length bs == 3 /\
   (match bs with
    | [d0; d1; d2] -> is_octal_digit d0 /\ is_octal_digit d1 /\ is_octal_digit d2 /\
                      octal_digit_to_int d0 * 64 +
                      octal_digit_to_int d1 * 8 +
                      octal_digit_to_int d2 == U8.v b
    | _ -> False))
  = lemma_octal_digit_roundtrip ();
    let v = U8.v b in
    assert (0 <= v / 64 /\ v / 64 <= 3);
    assert (0 <= (v / 8) % 8 /\ (v / 8) % 8 <= 7);
    assert (0 <= v % 8 /\ v % 8 <= 7)

(** Roundtrip proof *)

(** [encode_base08] distributes over list append. *)
let rec lemma_encode_base08_append (bs1 bs2: list UInt8.t) : Lemma
  (ensures encode_base08 (bs1 @ bs2) == encode_base08 bs1 @ encode_base08 bs2)
  (decreases bs1)
  = match bs1 with
    | [] -> ()
    | _ :: tl -> lemma_encode_base08_append tl bs2

(** Single byte roundtrip: decode(encode([b])) == Some([b]). *)
let lemma_base08_single_byte (b: UInt8.t) : Lemma
  (ensures decode_base08 (encode_base08 [b]) == Some [b])
  = lemma_encode_base08_single b;
    let v = U8.v b in
    let d0 = int_to_octal_digit (v / 64) in
    let d1 = int_to_octal_digit ((v / 8) % 8) in
    let d2 = int_to_octal_digit (v % 8) in
    assert (is_octal_digit d0 /\ is_octal_digit d1 /\ is_octal_digit d2);
    assert (octal_digit_to_int d0 * 64 +
            octal_digit_to_int d1 * 8 +
            octal_digit_to_int d2 == v);
    assert (U8.uint_to_t v == b)

(** Full roundtrip by induction on the input list. *)
let rec lemma_base08_roundtrip (bs: list UInt8.t) : Lemma
  (ensures decode_base08 (encode_base08 bs) == Some bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      lemma_base08_single_byte b;
      lemma_base08_roundtrip tl;
      lemma_encode_base08_append [b] tl

(** Concrete test vectors *)

(** "" -> "". *)
let lemma_base08_empty () : Lemma
  (ensures encode_base08 [] == [] /\
           decode_base08 [] == Some [])
  = ()

(** 0x00 -> "000". *)
let lemma_base08_zero () : Lemma
  (ensures encode_base08 [0x00uy] == [0x30uy; 0x30uy; 0x30uy])
  = lemma_octal_digit_roundtrip ()

(** 0xFF (255) -> "377". *)
let lemma_base08_ff () : Lemma
  (ensures encode_base08 [0xFFuy] == [0x33uy; 0x37uy; 0x37uy])
  = lemma_octal_digit_roundtrip ()

(** Decode "377" -> [0xFF]. *)
let lemma_base08_decode_377 () : Lemma
  (ensures decode_base08 [0x33uy; 0x37uy; 0x37uy] == Some [0xFFuy])
  = lemma_octal_digit_roundtrip ()

(** Error: non-multiple-of-3 input returns None. *)
let lemma_base08_decode_bad_length () : Lemma
  (ensures decode_base08 [0x30uy; 0x30uy] == None)
  = ()

(** Error: invalid octal char '8' returns None. *)
let lemma_base08_decode_invalid_char () : Lemma
  (ensures decode_base08 [0x38uy; 0x30uy; 0x30uy] == None)
  = ()

(** Error: overflow (>255) returns None.  "777" = 511 > 255. *)
let lemma_base08_decode_overflow () : Lemma
  (ensures decode_base08 [0x37uy; 0x37uy; 0x37uy] == None)
  = lemma_octal_digit_roundtrip ()

(** Roundtrip on concrete values. *)
let lemma_base08_roundtrip_concrete () : Lemma
  (ensures decode_base08 (encode_base08 [0x00uy; 0xFFuy; 0x7Fuy])
        == Some [0x00uy; 0xFFuy; 0x7Fuy])
  = lemma_base08_roundtrip [0x00uy; 0xFFuy; 0x7Fuy]
