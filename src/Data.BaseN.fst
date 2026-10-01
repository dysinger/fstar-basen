(* Copyright 2026 Department of Code LLC.
   SPDX-License-Identifier: AGPL-3.0-or-later *)

(**
Data.BaseN — RFC 4648 Base Encodings

Re-exports all four base encoding sub-modules with zero admits.
All four encodings use direct UInt8 arithmetic with list induction.
Base32/Base64 additionally import [Data.Codec.Types] for the [byte]
alias and [nat_of_int] helper.

Sub-modules (include order: Base08, Base16, Base32, Base64):
- [Data.BaseN.Base08] — Octal byte encoding (3 digits per byte)
- [Data.BaseN.Base16] — Hex encoding, uppercase canonical, no padding (RFC 4648 §8)
- [Data.BaseN.Base32] — Base32 encoding, A-Z + 2-7 alphabet, = padding (RFC 4648 §6)
- [Data.BaseN.Base64] — Base64 encoding, A-Z a-z 0-9 + /, = padding (RFC 4648 §4)

Note: Base32 and Base64 both define [pad_byte] and [is_pad] with identical
values (0x3D).  The second [include] intentionally shadows the first; both
definitions are semantically equivalent.

@header Data.BaseN
*)
module Data.BaseN

include Data.BaseN.Base08
include Data.BaseN.Base16
include Data.BaseN.Base32
include Data.BaseN.Base64
