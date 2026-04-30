# NIX_RUN is the wrapper put in front of every `lake` invocation. Each
# recipe passes its `lake` command as a single quoted argument, so
# NIX_RUN must accept "<wrapper> 'cmd'" semantics; the no-Nix path uses
# `sh -c` to keep the quoting form intact.
#
# The wrapper must put libsodium, libsecp256k1, and libblst on the
# compiler/linker path so Cryptograph.FFI's extern_lib targets can
# build. Two supported install paths (see README): your system package
# manager, or `nix-shell` via shell.nix.
#
# Auto-detection (overridable on the command line):
#   1. Already inside a nix-shell (IN_NIX_SHELL set) -> sh -c.
#   2. pkg-config finds libsodium + libsecp256k1     -> sh -c
#      (libblst typically tags along on the same system; the C build
#      surfaces a clear `blst.h` error if it doesn't).
#   3. nix-shell is on PATH                          -> nix-shell --run.
#   4. Otherwise                                     -> sh -c; let the
#      C build surface a missing-header error pointing at the README.
#
# Force a particular behaviour:
#     make NIX_RUN= build_all                        # no Nix wrapper
#     make NIX_RUN='nix-shell --run' build_all       # force Nix
ifeq ($(origin NIX_RUN), undefined)
  ifneq ($(IN_NIX_SHELL),)
    NIX_RUN := sh -c
  else ifeq ($(shell pkg-config --exists libsodium libsecp256k1 2>/dev/null && echo yes),yes)
    NIX_RUN := sh -c
  else ifneq ($(shell command -v nix-shell 2>/dev/null),)
    NIX_RUN := nix-shell --run
  else
    NIX_RUN := sh -c
  endif
else ifeq ($(strip $(NIX_RUN)),)
  # User passed `NIX_RUN=` to skip the wrapper; normalise to `sh -c` so
  # the recipes' single-quoted command form keeps working. `override`
  # is required because command-line assignments otherwise win against
  # in-Makefile assignments.
  override NIX_RUN := sh -c
endif

.PHONY: usage
usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
# Dev shell (Nix users only; system-package users skip this)
	@echo " - shell:              Enter the nix-shell with libsodium, libsecp256k1, libblst."
	@echo "                       Optional: skip if you've installed those libraries via your"
	@echo "                       system package manager (see README)."
# Cryptograph
	@echo " - build_cryptograph:  Build Cryptograph library (Lean modules + native extern_libs)."
	@echo " - clean_cryptograph:  Clean compiled lean files for Cryptograph."
	@echo " - check_cryptograph:  Same as build_cryptograph but also checks that each lean file"
	@echo "                       in Cryptograph is considered during compilation."
# Plutus Core
	@echo " - build_plutus_core:  Build PlutusCore formalization."
	@echo " - clean_plutus_core:  Clean compiled lean files for PlutusCore formalization."
	@echo " - check_plutus_core:  Same as build_plutus_core but also checks that each lean file"
	@echo "                       in the PlutusCore formalization is considered during compilation."
# Test suite
	@echo " - build_tests:        Build Test suite."
	@echo " - clean_tests:        Clean compiled lean files for the Test suite."
	@echo " - check_tests:        Same as build_tests but also checks that each lean file"
	@echo "                       in the Test suite is considered during compilation."
# Aggregates
	@echo " - build_all:          Build PlutusCore, Cryptograph, and Tests."
	@echo " - clean_all:          Clean everything."
	@echo " - check_all:          Run every check_* target."

# ------------------------------------------------------------------ #
# Dev shell                                                          #
# ------------------------------------------------------------------ #

.PHONY: shell
shell:
	nix-shell

# ------------------------------------------------------------------ #
# Cryptograph (Lean library + FFI extern_libs)                       #
# ------------------------------------------------------------------ #

.PHONY: build_cryptograph
build_cryptograph:
	$(NIX_RUN) 'lake build Cryptograph \
	            leanPlutusHash leanPlutusEd25519 \
	            leanPlutusSecp256k1 leanPlutusBls12_381'

.PHONY: clean_cryptograph
clean_cryptograph:
	$(NIX_RUN) 'lake clean'

.PHONY: check_cryptograph
check_cryptograph: clean_cryptograph
	$(NIX_RUN) './scripts/check_lean_project_compilation.sh Cryptograph TestVectors'

# ------------------------------------------------------------------ #
# PlutusCore                                                         #
# ------------------------------------------------------------------ #

.PHONY: build_plutus_core
build_plutus_core:
	$(NIX_RUN) 'lake build PlutusCore && lake build Lemmas'

.PHONY: clean_plutus_core
clean_plutus_core:
	$(NIX_RUN) 'lake clean'

.PHONY: check_plutus_core
check_plutus_core: clean_plutus_core
	$(NIX_RUN) './scripts/check_lean_project_with_lemmas.sh PlutusCore /Tests\.lean$$'

# ------------------------------------------------------------------ #
# Test suite                                                         #
# ------------------------------------------------------------------ #

.PHONY: build_tests
build_tests:
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 lake test'

.PHONY: clean_tests
clean_tests:
	$(NIX_RUN) 'lake clean'

.PHONY: check_tests
check_tests: clean_tests
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests'

# ------------------------------------------------------------------ #
# Aggregates                                                         #
# To maintain when you add new components                            #
# ------------------------------------------------------------------ #

.PHONY: build_all
build_all: build_plutus_core build_cryptograph build_tests

.PHONY: clean_all
clean_all: clean_plutus_core clean_cryptograph clean_tests

.PHONY: check_all
check_all: check_plutus_core check_cryptograph check_tests
