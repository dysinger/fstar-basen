# Copyright 2026 Department of Code LLC.
# SPDX-License-Identifier: AGPL-3.0-or-later

# fstar-basen — dev-loop build (F* verify + KaRaMeL extract).
# Usage: nix develop, then `make check` / `make krml`.

FSTAR ?= fstar.exe
KRML  ?= krml

ULIB        ?= $(shell $(FSTAR) --locate_lib 2>/dev/null || echo /none)/ulib
KRM_LIB_DIR ?= $(or $(KRML_HOME)/krmllib,$(KRM_LIB))

# The codec dependency (Data.Codec.Types) is vendored in-repo as ./codec.
CODEC_SRC ?= ./codec

FSTAR_FLAGS = --no_default_includes \
  --include $(ULIB) \
  --include ./src \
  --include $(CODEC_SRC)/src \
  --include $(KRM_LIB_DIR) \
  --include $(KRM_LIB_DIR)/obj

# Source modules in DEPENDENCY ORDER (leaf modules first).
SRC_MODS := Data.BaseN.Base08 Data.BaseN.Base16 Data.BaseN.Base32 \
            Data.BaseN.Base64 Data.BaseN Data.BaseN.Low
TST_MODS := Data.BaseN.Test.Integration

# Only Low* modules extracted to C (src/ only).
KRML_MODS := Data.BaseN.Low

.PHONY: check krml clean

check: $(addprefix out/checked/,$(addsuffix .fst.checked,$(SRC_MODS))) \
       $(addprefix out/checked/,$(addsuffix .fst.checked,$(TST_MODS)))

out/checked/%.fst.checked: src/%.fst
	@mkdir -p out/checked
	@test -n "$(FSTAR_CHECKED)" || { \
	  echo "ERROR: FSTAR_CHECKED is not set; run \`nix develop\` first" >&2; \
	  exit 1; }
	@cp $(FSTAR_CHECKED)/*.checked out/checked/ 2>/dev/null || true
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) \
	  --z3rlimit 80 \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/checked $<

out/checked/%.fst.checked: test/%.fst
	@mkdir -p out/checked
	@test -n "$(FSTAR_CHECKED)" || { \
	  echo "ERROR: FSTAR_CHECKED is not set; run \`nix develop\` first" >&2; \
	  exit 1; }
	@cp $(FSTAR_CHECKED)/*.checked out/checked/ 2>/dev/null || true
	@echo "=== $* ==="
	$(FSTAR) $(FSTAR_FLAGS) --include ./test \
	  --z3rlimit 80 \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/checked $<

krml: check $(addprefix out/krml/,$(addsuffix .krml,$(subst .,_,$(KRML_MODS))))

# Per-module krml extraction — dots in source, underscores in output.
define KRML_RULE
out/krml/$(subst .,_,$(1)).krml: src/$(1).fst
	@mkdir -p out/krml
	$(FSTAR) $(FSTAR_FLAGS) \
	  --cache_checked_modules --cache_dir out/checked \
	  --odir out/krml --codegen krml \
	  --extract_module $(1) $$<
endef
$(foreach mod,$(KRML_MODS),$(eval $(call KRML_RULE,$(mod))))

clean:
	rm -rf out
