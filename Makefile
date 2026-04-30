# All lake invocations are wrapped in `nix-shell --run` so the native
# crypto libraries (libsodium, libsecp256k1, libblst) required by
# Cryptograph's extern_lib targets are on the compiler/linker path.
#
# Override NIX_RUN= (empty) to skip the wrapper if you're already inside
# a shell that has those libraries, e.g.
#     make NIX_RUN= build_all
NIX_RUN ?= nix-shell --run

.PHONY: usage
usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
# Dev shell
	@echo " - shell:              Enter the nix-shell with libsodium, libsecp256k1, libblst."
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
