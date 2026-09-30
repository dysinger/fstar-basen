(**
Data.BaseN.Test.Integration — Binds all basen lemmas + tests.

If any lemma or test function is deleted or renamed, F* verification fails.
This guarantees mechanically-enforced test coverage.

Uses [--admit_smt_queries true] for integration anchoring only.
Individual lemmas are proven without admits in their source modules.

Section ordering matches the include order in Data.BaseN.fst:
  Base08 → Base16 → Base32 → Base64 → Pulse

@header Data.BaseN.Test.Integration
*)
module Data.BaseN.Test.Integration

open Data.BaseN
open Data.BaseN.Pulse

#push-options "--admit_smt_queries true"

(** Base08 lemmas *)

let _lemma_octal_digit_roundtrip = lemma_octal_digit_roundtrip
let _lemma_encode_base08_single = lemma_encode_base08_single
let _lemma_encode_base08_append = lemma_encode_base08_append
let _lemma_base08_single_byte = lemma_base08_single_byte
let _lemma_base08_roundtrip = lemma_base08_roundtrip

(** Base08 concrete test vectors *)

let _lemma_base08_empty = lemma_base08_empty
let _lemma_base08_zero = lemma_base08_zero
let _lemma_base08_ff = lemma_base08_ff
let _lemma_base08_decode_377 = lemma_base08_decode_377
let _lemma_base08_decode_bad_length = lemma_base08_decode_bad_length
let _lemma_base08_decode_invalid_char = lemma_base08_decode_invalid_char
let _lemma_base08_decode_overflow = lemma_base08_decode_overflow
let _lemma_base08_roundtrip_concrete = lemma_base08_roundtrip_concrete

(** Base16 lemmas *)

let _lemma_nibble_roundtrip = lemma_nibble_roundtrip
let _lemma_encode_base16_single = lemma_encode_base16_single
let _lemma_encode_base16_append = lemma_encode_base16_append
let _lemma_base16_single_byte = lemma_base16_single_byte
let _lemma_base16_roundtrip = lemma_base16_roundtrip

(** Base16 concrete test vectors *)

let _lemma_base16_empty = lemma_base16_empty
let _lemma_base16_f = lemma_base16_f
let _lemma_base16_fo = lemma_base16_fo
let _lemma_base16_foo = lemma_base16_foo
let _lemma_base16_decode_66 = lemma_base16_decode_66
let _lemma_base16_decode_666F = lemma_base16_decode_666F
let _lemma_base16_decode_lowercase = lemma_base16_decode_lowercase
let _lemma_base16_decode_uppercase = lemma_base16_decode_uppercase
let _lemma_base16_decode_odd_length = lemma_base16_decode_odd_length
let _lemma_base16_decode_invalid_char = lemma_base16_decode_invalid_char
let _lemma_base16_roundtrip_concrete = lemma_base16_roundtrip_concrete

(** Base32 helper lemmas *)

let _lemma_b32_char_roundtrip = lemma_b32_char_roundtrip
let _lemma_b32_val_not_pad = lemma_b32_val_not_pad
let _lemma_b32_val_is_char = lemma_b32_val_is_char
let _lemma_b32_byte0 = lemma_b32_byte0
let _lemma_b32_byte1 = lemma_b32_byte1
let _lemma_b32_byte2 = lemma_b32_byte2
let _lemma_b32_byte3 = lemma_b32_byte3
let _lemma_b32_byte4 = lemma_b32_byte4

(** Base32 roundtrip lemmas *)

let _lemma_decode_base32_group_quintet = lemma_decode_base32_group_quintet
let _lemma_base32_single = lemma_base32_single
let _lemma_base32_pair = lemma_base32_pair
let _lemma_base32_triple = lemma_base32_triple
let _lemma_base32_quad = lemma_base32_quad
let _lemma_base32_quintet = lemma_base32_quintet
let _lemma_base32_roundtrip = lemma_base32_roundtrip

(** Base32 concrete test vectors *)

let _lemma_base32_empty = lemma_base32_empty
let _lemma_base32_f = lemma_base32_f
let _lemma_base32_fo = lemma_base32_fo
let _lemma_base32_foo = lemma_base32_foo
let _lemma_base32_foob = lemma_base32_foob
let _lemma_base32_fooba = lemma_base32_fooba
let _lemma_base32_foobar = lemma_base32_foobar
let _lemma_base32_decode_f = lemma_base32_decode_f
let _lemma_base32_decode_fooba = lemma_base32_decode_fooba
let _lemma_base32_decode_invalid_char = lemma_base32_decode_invalid_char
let _lemma_base32_decode_pad_first = lemma_base32_decode_pad_first
let _lemma_base32_decode_bad_length = lemma_base32_decode_bad_length
let _lemma_base32_roundtrip_concrete = lemma_base32_roundtrip_concrete

(** Base64 lemmas *)

let _lemma_b64_char_roundtrip = lemma_b64_char_roundtrip
let _lemma_b64_val_not_pad = lemma_b64_val_not_pad
let _lemma_b64_val_is_char = lemma_b64_val_is_char
let _lemma_b64_byte0 = lemma_b64_byte0
let _lemma_b64_byte1 = lemma_b64_byte1
let _lemma_b64_byte2 = lemma_b64_byte2
let _lemma_base64_single = lemma_base64_single
let _lemma_base64_pair = lemma_base64_pair
let _lemma_base64_triple = lemma_base64_triple
let _lemma_base64_roundtrip = lemma_base64_roundtrip

(** Base64 concrete test vectors *)

let _lemma_base64_empty = lemma_base64_empty
let _lemma_base64_f = lemma_base64_f
let _lemma_base64_fo = lemma_base64_fo
let _lemma_base64_foo = lemma_base64_foo
let _lemma_base64_foob = lemma_base64_foob
let _lemma_base64_fooba = lemma_base64_fooba
let _lemma_base64_foobar = lemma_base64_foobar
let _lemma_base64_decode_f = lemma_base64_decode_f
let _lemma_base64_decode_foo = lemma_base64_decode_foo
let _lemma_base64_decode_invalid_char = lemma_base64_decode_invalid_char
let _lemma_base64_decode_pad_first = lemma_base64_decode_pad_first
let _lemma_base64_decode_bad_length = lemma_base64_decode_bad_length
let _lemma_base64_roundtrip_concrete = lemma_base64_roundtrip_concrete

(** Pulse lemmas *)

let _lemma_hex_digit_eq_nibble = lemma_hex_digit_eq_nibble
let _lemma_pulse_hex_roundtrip = lemma_hex_roundtrip
let _lemma_b64_val_i_eq_b64_val = lemma_b64_val_i_eq_b64_val
let _lemma_pulse_base16_roundtrip = lemma_pulse_base16_roundtrip
let _lemma_pulse_base64_triple_roundtrip = lemma_pulse_base64_triple_roundtrip
let _lemma_pulse_base64_tail1_roundtrip = lemma_pulse_base64_tail1_roundtrip
let _lemma_pulse_base64_tail2_roundtrip = lemma_pulse_base64_tail2_roundtrip

(** Pulse encode/decode functions — mechanically protected against deletion *)

let _encode_base16 = encode_base16
let _decode_base16 = decode_base16
let _encode_base64_triple = encode_base64_triple
let _encode_base64_tail1 = encode_base64_tail1
let _encode_base64_tail2 = encode_base64_tail2
let _decode_base64_quad = decode_base64_quad

#pop-options
