.PHONY: usage

usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
	@echo " - Plutus core"
	@echo "   - build_plutus_core: Build PlutusCore formalization."
	@echo "   - clean_plutus_core: Clean compiled lean files for PlutusCore formalization."
	@echo "   - check_plutus_core: Same as build_plutus_core but also checks that each lean file"
	@echo "                        in the PlutusCore formalization is considered during compilation."
# Test suite
	@echo " - Tests"
	@echo "   - build_tests: Build Test suite."
	@echo "   - clean_tests: Clean compiled lean files for the Test suite."
	@echo "   - check_tests: Same as build_tests but also checks that each lean file"
	@echo "                  in the Test suite is considered during compilation."
# Conformance test generator
	@echo " - Conformance tests"
	@echo "   - gen_conformance_tests: (Re)generate the conformance test suite under"
	@echo "                            Tests/Conformance/Generated/ from CONFORMANCE_ROOT"
	@echo "                            (default: .plutus-conformance/plutus-conformance)."
	@echo "                            Pass excludeNotImplemented=1 to skip test"
	@echo "                            categories whose features are not yet"
	@echo "                            implemented in this Lean formalization."
	@echo "   - build_conformance: Build the conformance test suite (Tests.Conformance)."
	@echo "   - check_conformance: Same as build_conformance but also checks that each"
	@echo "                        lean file under Tests/Conformance/ is considered"
	@echo "                        during compilation. Requires .plutus-conformance"
	@echo "                        symlink and a previously generated test suite."

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
	lake test

.PHONY: clean_tests
clean_tests:
	lake clean

.PHONY: check_tests
check_tests: clean_tests
	./scripts/check_lean_project_compilation.sh Tests Tests Tests/Conformance

# Path to the plutus-conformance directory containing test-cases/.
CONFORMANCE_ROOT ?= .plutus-conformance/plutus-conformance
# Path string embedded in generated #import_uplc lines (interpreted at test-build time).
CONFORMANCE_EMBED_ROOT ?= .plutus-conformance/plutus-conformance

# Optional: set excludeNotImplemented=1 (or any non-empty value) to skip test
# categories whose underlying features are not yet implemented in this Lean
# formalization.
ifneq ($(strip $(excludeNotImplemented)),)
EXCLUDE_NOT_IMPLEMENTED_FLAG := --exclude-not-implemented
else
EXCLUDE_NOT_IMPLEMENTED_FLAG :=
endif

.PHONY: gen_conformance_tests
gen_conformance_tests:
	lake build gen_conformance_tests
	lake exe gen_conformance_tests $(CONFORMANCE_ROOT) \
		--out Tests/Conformance/Generated \
		--embed-root $(CONFORMANCE_EMBED_ROOT) \
		$(EXCLUDE_NOT_IMPLEMENTED_FLAG)

.PHONY: build_conformance
build_conformance:
	lake build Tests.Conformance

.PHONY: check_conformance
check_conformance: clean_tests
	./scripts/check_lean_project_compilation.sh Tests.Conformance Tests/Conformance

# Aggregate commands
# To maintain when you add new components
.PHONY: build_all
build_all: build_plutus_core build_tests

.PHONY: clean_all
clean_all: clean_plutus_core clean_tests

.PHONY: check_all
check_all: check_plutus_core check_tests
