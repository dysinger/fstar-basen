# Changelog

All notable changes to this project are documented in this file.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- Renamed the C leaf `Data.BaseN.Low` → `Data.BaseN.Pulse` (the KaRaMeL `.Low`
  convention is retired; the Pulse/Custard layer is the successor).
- Ported the encode/decode leaf from KaRaMeL Low\* (`Stack` + `LowStar.Buffer`)
  to Pulse (`fn` + `Pulse.Lib.Array`), 0-admit, extracting to C11 via Custard.
- Rolled F\* forward to `v2026.09.20+lsp` (first stable tag shipping the
  Custard extractor).
- Removed the KaRaMeL/Low\* toolchain and all its targets (`krml`, `native`,
  `rust`, `wasm`) — F\* `v2026.09.20` deleted the `FStar.HyperStack` /
  `LowStar.Buffer` stdlib.

### Source drift fixes

- Removed `open FStar.Mul` and `Prims.op_Multiply` (both deleted upstream).
- Removed `--split_queries always` from `#push-options` (option deleted).

## [0.1.0] — initial extraction

### Added

- Extracted `Data.BaseN` out of the original monorepo into a standalone
  repository built from `fstar-nix-flake-template`.
- Source modules:
  - `Data.BaseN` — the base-N facade.
  - `Data.BaseN.Base08` / `Base16` / `Base32` / `Base64` — the RFC 4648
    alphabets and codecs.
  - `Data.BaseN.Pulse` — C-extractable encode/decode leaf.
- Test module: `Data.BaseN.Test.Integration`.
- Nix flake targets: `.#checked`, `.#ocaml`, `.#native`, `.#fsharp`.
- Dual licensing: AGPL-3.0-or-later, or a commercial license from the author.

### Notes

- Zero admits / zero magic / zero `assume` across all modules.
