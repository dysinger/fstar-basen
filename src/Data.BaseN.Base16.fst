(**
Data.BaseN.Base16 — RFC 4648 §8 Hex Encoding

Copyright 2026 Department of Code LLC. All rights reserved.

Built directly on UInt8 arithmetic with list induction.
ZERO admits. ZERO --admit_smt_queries. 100% lemmas proven.

Architecture:
- is_hex, nibble_to_upper_hex, hex_char_to_nibble: char ↔ nibble
- encode_base16: each byte → 2 uppercase hex chars
- decode_base16: parse pairs of hex chars → bytes
- lemma_base16_roundtrip: structural induction on input list

@header Data.BaseN.Base16
*)
module Data.BaseN.Base16

open FStar.UInt8
open FStar.List.Tot
open FStar.Mul

module U8 = FStar.UInt8
module L = FStar.List.Tot

(** Character predicates *)

(** [is_hex b] is true when byte [b] is an ASCII hex digit (0-9, A-F, a-f). *)
let is_hex (b: UInt8.t) : bool =
  let v = U8.v b in
  (0x30 <= v && v <= 0x39) || (0x41 <= v && v <= 0x46) || (0x61 <= v && v <= 0x66)

(** [nibble_to_upper_hex n] converts a nibble 0-15 to uppercase ASCII hex (0-9, A-F).
    @param n Nibble value, must be in [0, 15]. *)
let nibble_to_upper_hex (n: int{0 <= n /\ n <= 15}) : Tot UInt8.t =
  if n <= 9 then U8.uint_to_t (0x30 + n) else U8.uint_to_t (0x37 + n)

(** [hex_char_to_nibble b] converts an ASCII hex digit to its integer value.
    @param b Byte satisfying [is_hex].
    @returns Integer in [0, 15]. *)
let hex_char_to_nibble (b: UInt8.t{is_hex b}) : n:int{0 <= n /\ n <= 15} =
  let v = U8.v b in
  if 0x30 <= v && v <= 0x39 then v - 0x30
  else if 0x41 <= v && v <= 0x46 then v - 0x37
  else v - 0x57

(** encode_base16 / decode_base16 *)

(** [encode_base16] encodes each byte as two uppercase hex chars (RFC 4648 §8).
    @param bs Input byte list.
    @returns List of hex character bytes. *)
let encode_base16 (bs: list UInt8.t) : list UInt8.t =
  L.flatten (L.map (fun (b: UInt8.t) ->
    let v = U8.v b in
    [nibble_to_upper_hex (v / 16); nibble_to_upper_hex (v % 16)]
  ) bs)

(** [decode_base16] parses pairs of hex chars into bytes.
    (* Two hex digits always produce 0..255 — no overflow check needed,
       unlike Base08 where three octal digits can exceed 255. *)
    @param bs Input hex character list.
    @returns [Some bytes] on success, [None] on odd length or non-hex char. *)
let rec decode_base16 (bs: list UInt8.t) : Tot (option (list UInt8.t)) (decreases (L.length bs)) =
  match bs with
  | [] -> Some []
  | hi :: lo :: rest ->
    if is_hex hi && is_hex lo then
      let n = hex_char_to_nibble hi * 16 + hex_char_to_nibble lo in
      assert (0 <= n /\ n <= 255);
      (match decode_base16 rest with
       | Some tl -> Some (U8.uint_to_t n :: tl)
       | None -> None)
    else None
  | _ -> None

(** Nibble conversion lemmas *)

(** Each nibble 0-15 maps to a valid hex character, and converts back losslessly. *)
let lemma_nibble_roundtrip () : Lemma
  (ensures (forall (i: int{0 <= i /\ i <= 15}). hex_char_to_nibble (nibble_to_upper_hex i) == i /\
                                                  is_hex (nibble_to_upper_hex i)))
  = ()

(** [encode_base16] of a single byte produces exactly 2 valid hex characters. *)
let lemma_encode_base16_single (b: UInt8.t) : Lemma
  (let bs = encode_base16 [b] in
   L.length bs == 2 /\
   (match bs with
    | [hi; lo] -> is_hex hi /\ is_hex lo /\
                  hex_char_to_nibble hi * 16 + hex_char_to_nibble lo == U8.v b
    | _ -> False))
  = lemma_nibble_roundtrip ();
    let v = U8.v b in
    assert (0 <= v / 16 /\ v / 16 <= 15);
    assert (0 <= v % 16 /\ v % 16 <= 15)

(** Roundtrip proof *)

(** [encode_base16] distributes over list append. *)
let rec lemma_encode_base16_append (bs1 bs2: list UInt8.t) : Lemma
  (ensures encode_base16 (bs1 @ bs2) == encode_base16 bs1 @ encode_base16 bs2)
  (decreases bs1)
  = match bs1 with
    | [] -> ()
    | _ :: tl -> lemma_encode_base16_append tl bs2

(** Single byte roundtrip: decode(encode([b])) == Some([b]). *)
let lemma_base16_single_byte (b: UInt8.t) : Lemma
  (ensures decode_base16 (encode_base16 [b]) == Some [b])
  = lemma_encode_base16_single b;
    let v = U8.v b in
    let hi = nibble_to_upper_hex (v / 16) in
    let lo = nibble_to_upper_hex (v % 16) in
    assert (is_hex hi /\ is_hex lo);
    assert (hex_char_to_nibble hi * 16 + hex_char_to_nibble lo == v);
    assert (U8.uint_to_t v == b)

(** Full roundtrip by induction on the input list. *)
let rec lemma_base16_roundtrip (bs: list UInt8.t) : Lemma
  (ensures decode_base16 (encode_base16 bs) == Some bs)
  (decreases bs)
  = match bs with
    | [] -> ()
    | b :: tl ->
      lemma_base16_single_byte b;
      lemma_base16_roundtrip tl;
      lemma_encode_base16_append [b] tl

(** Concrete test vectors — RFC 4648 §10 *)

(** "" -> "". *)
let lemma_base16_empty () : Lemma
  (ensures encode_base16 [] == [] /\
           decode_base16 [] == Some [])
  = ()

(** "f" -> "66" (0x66 = 'f'). *)
let lemma_base16_f () : Lemma
  (ensures encode_base16 [0x66uy] == [0x36uy; 0x36uy])
  = lemma_nibble_roundtrip ()

(** "fo" -> "666F". *)
let lemma_base16_fo () : Lemma
  (ensures encode_base16 [0x66uy; 0x6Fuy] == [0x36uy; 0x36uy; 0x36uy; 0x46uy])
  = lemma_nibble_roundtrip ()

(** "foo" -> "666F6F". *)
let lemma_base16_foo () : Lemma
  (ensures encode_base16 [0x66uy; 0x6Fuy; 0x6Fuy]
        == [0x36uy; 0x36uy; 0x36uy; 0x46uy; 0x36uy; 0x46uy])
  = lemma_nibble_roundtrip ()

(** Decode "66" -> [0x66]. *)
let lemma_base16_decode_66 () : Lemma
  (ensures decode_base16 [0x36uy; 0x36uy] == Some [0x66uy])
  = lemma_nibble_roundtrip ()

(** Decode lowercase "6a" -> [0x6A]. *)
let lemma_base16_decode_lowercase () : Lemma
  (ensures decode_base16 [0x36uy; 0x61uy] == Some [0x6Auy])
  = lemma_nibble_roundtrip ()

(** Decode uppercase "6F" -> [0x6F]. *)
let lemma_base16_decode_uppercase () : Lemma
  (ensures decode_base16 [0x36uy; 0x46uy] == Some [0x6Fuy])
  = lemma_nibble_roundtrip ()

(** Error: odd-length hex input returns None. *)
let lemma_base16_decode_odd_length () : Lemma
  (ensures decode_base16 [0x36uy] == None)
  = ()

(** Error: invalid hex char 'G' returns None. *)
let lemma_base16_decode_invalid_char () : Lemma
  (ensures decode_base16 [0x47uy; 0x47uy] == None)
  = ()

(** Decode "666F" -> [0x66; 0x6F]. *)
let lemma_base16_decode_666F () : Lemma
  (ensures decode_base16 [0x36uy; 0x36uy; 0x36uy; 0x46uy] == Some [0x66uy; 0x6Fuy])
  = lemma_nibble_roundtrip ()

(** Roundtrip on concrete values. *)
let lemma_base16_roundtrip_concrete () : Lemma
  (ensures decode_base16 (encode_base16 [0x00uy; 0xFFuy; 0xABuy])
        == Some [0x00uy; 0xFFuy; 0xABuy])
  = lemma_base16_roundtrip [0x00uy; 0xFFuy; 0xABuy]
