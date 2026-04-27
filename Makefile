.PHONY: usage

usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
# Plutus Core
	@echo " - build_plutus_core: Build PlutusCore formalization."
	@echo " - clean_plutus_core: Clean compiled lean files for PlutusCore formalization."
	@echo " - check_plutus_core: Same as build_plutus_core but also checks that each lean file"
	@echo "                      in the PlutusCore formalization is considered during compilation."
# Test suite
	@echo " - build_tests: Build Test suite."
	@echo " - clean_tests: Clean compiled lean files for the Test suite."
	@echo " - check_tests: Same as build_tests but also checks that each lean file"
	@echo "                in the Test suite is considered during compilation."

.PHONY: build_plutus_core
build_plutus_core:
	lake build PlutusCore; lake build Lemmas

.PHONY: clean_plutus_core
clean_plutus_core:
	lake clean

.PHONY: check_plutus_core
check_plutus_core: clean_plutus_core
	./scripts/check_lean_project_with_lemmas.sh PlutusCore

.PHONY: build_tests
build_tests:
	LEAN_NUM_THREADS=5 lake test

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests: clean_tests
	LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_plutus_core build_tests

.PHONY: clean_all
clean_all: clean_plutus_core clean_tests

.PHONY: check_all
check_all: check_plutus_core check_tests
