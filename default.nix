# fstar-basen — Data.BaseN library: verified base-N codecs (KaRaMeL era)
#
# Takes pkgs with fstar, karamel, fstar-checked in scope (from the flake
# overlay), plus the vendored codec dependency's checked set + source path.
#
# Returns { basen-checked; basen-krml }.

{ pkgs, codec-checked, codec-src }:

let
  inherit (pkgs) stdenv fstar karamel fstar-checked;

  fstar-exe = "${fstar}/bin/fstar.exe";
  ulib = "${fstar}/lib/fstar/ulib";
  krmllib = "${karamel.home}/krmllib";

  fstar-flags = "--no_default_includes --include ${ulib} --include ./src --include ${codec-src}/src --include ${krmllib} --include ${krmllib}/obj --z3rlimit 80";

  # Source modules in DEPENDENCY ORDER (leaf modules first).
  ordered-src-modules = [
    "Data.BaseN.Base08"
    "Data.BaseN.Base16"
    "Data.BaseN.Base32"
    "Data.BaseN.Base64"
    "Data.BaseN"
    "Data.BaseN.Low"
  ];

  basen-checked = stdenv.mkDerivation {
    pname = "basen-checked";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
      cp ${fstar-checked}/*.checked $out/ 2>/dev/null || true
      cp ${codec-checked}/*.checked $out/ 2>/dev/null || true

      for mod in ${builtins.concatStringsSep " " ordered-src-modules}; do
        echo "=== Verifying $mod ==="
        ${fstar-exe} ${fstar-flags} \
          --cache_checked_modules --cache_dir $out --odir $out \
          src/$mod.fst || exit 1
      done
      # Test module (Integration anchors).
      echo "=== Verifying Data.BaseN.Test.Integration ==="
      ${fstar-exe} ${fstar-flags} --include ./test \
        --cache_checked_modules --cache_dir $out --odir $out \
        test/Data.BaseN.Test.Integration.fst || exit 1
      rm -f $out/*.krml $out/*.c $out/*.h 2>/dev/null || true
      echo "checked: $(ls $out/*.checked 2>/dev/null | wc -l) files"
    '';
    installPhase = "true";
  };

  basen-krml = stdenv.mkDerivation {
    pname = "basen-krml";
    version = "0.1.0";
    src = ./.;
    nativeBuildInputs = [ fstar ];
    buildPhase = ''
      mkdir -p $out
      cp ${basen-checked}/*.checked $out/ 2>/dev/null || true
      cp ${codec-checked}/*.checked $out/ 2>/dev/null || true
      cp ${fstar-checked}/*.checked $out/ 2>/dev/null || true

      for mod in $(grep -h '^module' src/*.fst | grep -v ' = ' | grep '\.Low' | sed 's/module //'); do
        echo "=== Extracting $mod ==="
        ${fstar-exe} ${fstar-flags} \
          --cache_checked_modules --cache_dir $out \
          --odir $out --codegen krml \
          --extract_module $mod \
          src/$mod.fst || exit 1
      done
      rm -f $out/*.checked $out/*.c $out/*.h $out/*.exe 2>/dev/null || true
      echo "krml: $(ls $out/*.krml 2>/dev/null | wc -l) files"
    '';
    installPhase = "true";
  };
in
{
  inherit basen-checked basen-krml;
}
