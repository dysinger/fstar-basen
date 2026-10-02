# basen — Agent Guide & Handoff

`Data.BaseN` — verified base-N encodings (RFC 4648), extracted from the xeno
monorepo (`basen/`) as a standalone repo.  Part of `extract-ported-packages`
Round 1 (T1.3), following `codec` (T1.2).  F* source is 0-admit.

## ⛔ MANDATES (binding — read before doing anything)

1. **NEVER run `fstar.exe`, `nix build`, or `make` in the foreground.**  They
   can hang forever.  **Always** run them **detached** and poll the log:

   ```bash
   cd /Users/user/_/basen
   rm -f /tmp/basen-build.log
   nohup nix build .#checked --print-out-paths --no-link > /tmp/basen-build.log 2>&1 &
   # … poll: cat /tmp/basen-build.log ; ps -p $!
   ```

   A stuck process (0% CPU `stopped`, or 100% CPU spin) is a hang — kill it,
   diagnose, don't wait.  Per-step budgets: fstar verify ≤ 10 min, `nix build`
   ≤ 15 min (but the F\* bootstrap itself takes ~20 min *only on first build*;
   it is now cached, so don't re-trigger it — see "The re-bootstrap landmine").

2. **The codec dep pin.**  `flake.nix` consumes `codec` from the
   published `github:dysinger/fstar-codec` repo (pinned to HEAD in
   flake.lock).  Its `checked` package's `.checked` set is injected as
   `codec-checked`; its source tree as `codec-src` (for `--include`).

3. **Do not edit `codec`'s `buildPhase`/`installPhase` comments.**  The
   F\* overlay in `flake.nix` MUST stay **byte-identical** to codec's
   (see "The re-bootstrap landmine" below).  Any comment/whitespace change to
   those strings changes the derivation hash and forces a full F\* bootstrap.

## ✅ Current state (this session — Pulse port DONE, 4/4 targets GREEN)

### The re-bootstrap landmine (FIXED this session)

`nix build` was re-bootstrapping F\* from source because my initial `flake.nix`
had **rewritten the comments** in the F\* overlay's `buildPhase`/`installPhase`,
changing the derivation hash (nix embeds those strings verbatim).  The F\*
pin (`cf847952…`, `v2026.09.20+lsp`) was *already* cached from codec's
build.  **Fix:** the overlay is now byte-identical to codec's.  Do NOT
touch those strings.

### `Data.BaseN.Pulse` is PORTED to Pulse (this session)

The old `Data.BaseN.Low` (KaRaMeL Low\*: `FStar.HyperStack.ST`,
`LowStar.Buffer`, `Stack`) was **deleted** (Low\* stdlib removed in
`v2026.09.20`).  Replaced by `src/Data.BaseN.Pulse.fst` (`#lang-pulse`),
**0-admit verified**.

The Pulse idiom (learned the hard way this session — mirror `codec`'s
`Data.Codec.Pulse`):

- **Pulse runtime-body syntax differs from pure F\*:**
  - `let x = e;` (statement form) — NOT `let x = e in`.
  - `if COND { } else { }` (brace form) — NOT `if … then … else`.
  - `match scrutinee { | Pat -> { body } … }` (brace arms) — NOT `match … with`.
  - No `||`/`&&`/`=`/`<` in body conditions — use `U8.eq`/`U32.lt`/`U32.eq`,
    or lift boolean logic into pure `Tot` helpers (e.g. `is_pad_pair`).
  - `match (a, b) with` (tuple scrutinee) is NOT valid; use nested single
    scrutinees.
- **No `U8.v`/`U32.v`/nat `%` in extracted bodies** (Error 368 — `Prims.int`
  has no C repr).  Use `FStar.Int.Cast.uint32_to_uint8` /
  `uint8_to_uint32` + `U32.div`/`U32.rem`/`U32.mul`/`U32.add`/`U32.sub`.
  (`U32.v`/`U8.v` are FINE in `requires`/`ensures`/`noextract` spec positions.)
- **No `list`/`Prims.int` in extracted result types.**  `opt_result_bytes`
  originally carried `list U8.t`; it now carries a C-representable record
  `bytes3 = { n: U32.t; b0: U8.t; b1: U8.t; b2: U8.t }`.
- **Decode postconditions use `noextract` pure spec functions** mirroring the
  body exactly (`decode_base16_spec` / `decode_base64_quad_spec`), with
  `ensures … r == <spec> (Seq.slice s0 off (off+n))`.  Roundtrip lemmas call
  `noextract` pure spec-roundtrip lemmas (`lemma_decode_*_spec_roundtrip`).
- **`U8.uint_to_t` has a `< 256` precondition** in extracted bodies; use a
  narrow type (`opt_nibble` = `< 16`) or `uint32_to_uint8` (truncating, no
  precondition) so SMT can discharge the bound.

### Build matrix (this session)

| Target | Status | Output |
|---|---|---|
| `checked` | ✅ GREEN 0-admit | 7 `Data.BaseN*.checked` (Base08/16/32/64, facade, Pulse, Integration) |
| `native` (C) | ✅ GREEN | `Custard.c`/`Custard.h`/`basen.h`, `libbasen.{dylib,a}` (C11, no karamel) |
| `fsharp` (.NET) | ✅ GREEN | `Custard.dll` (`.NET 10`) |
| `ocaml` | ✅ GREEN | findlib `basen-ocaml` |

Target names match codec / fstar-nix-flake-template master:
`default = native`, `checked`, `ocaml`, `native`, `fsharp`.
`nix flake check` and `nix fmt` are GREEN (treefmt wired in, matching
codec).

### RESOLVED — `ocaml` cross-repo dep (was deferral T0.2)

`nix build .#ocaml` previously failed at the dune step: the F\*-extracted
`Data_BaseN_Base32.ml` / `Data_BaseN_Base64.ml` reference
`Data_Codec_Types.nat_of_int`, but `codec-ocaml` (the `codec` findlib
package) wraps its modules into a `Codec.*` namespace (dune `(wrapped true)`
default), so the raw `Data_Codec_Types` module name is unbound.

**Fix (landed):** instead of consuming `codec-ocaml`, the `ocaml-src` derivation
now extracts the codec's **pure spec** (`Data.Codec.Types` + `Data.Codec`)
locally via `--codegen OCaml` from `codec-src`, compiles them into the
`basen-ocaml` dune library alongside basen's own modules, and drops the
`codec-ocaml` findlib dependency.  No `Custard` collision: only the codec *pure*
spec is extracted, never its Pulse leaf.  This is the same "compile the codec
spec locally, unwrapped" shape `codec` itself uses (there `pure-modules`
*is* the codec spec).

## Build commands

```bash
nix build .#checked    # F* verification gate (0-admit)
nix build .#native     # C11 shared/static lib (default)
nix build .#fsharp     # .NET library
nix build .#ocaml      # OCaml findlib package
nix fmt                 # format nix files (treefmt)
nix develop && make check   # dev loop (no nix)
```

## Reference

- Canonical reference: `../codec` (its `Data.Codec.Pulse`, `flake.nix`,
  `default.nix`, `Makefile` are the Custard-era shape this repo mirrors).
- The F\* skill: `~/.pi/agent/skills/fstar/fstar-2026.09.20/SKILL.md`
  (Custard, Pulse idiom, `U8.v`/`U32.v` → `Int.Cast`, the dead-Low\* delta).
- The xeno openspec: `xeno/openspec/changes/extract-ported-packages/` (T1.3).
