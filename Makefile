# Root Makefile — entry point for skill validation
#
# Usage:
#   make verify       Run every skill's examples/Makefile verify target
#   make list-skills  Print the discovered skill list (skips _-prefixed dirs)
#   make help         Show this help

SHELL := /bin/sh

# Repo root is wherever this Makefile lives. Computed once; passed to
# every recursive $(MAKE) invocation so sub-Makefiles don't have to
# guess via $(MAKEFILE_LIST).
REPO_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))

# Discover skills: any subdirectory of .agent/skills/ whose name does
# NOT start with `_`. The underscore convention is documented in
# .agent/skills/_templates/README.md and spec §6.3.
ALL_SKILL_DIRS := $(patsubst %/,%,$(wildcard .agent/skills/*/))
SKILLS         := $(sort $(filter-out _%,$(notdir $(ALL_SKILL_DIRS))))

# Build the list of examples/ that actually exist. A skill without an
# examples/ dir simply doesn't appear here — it doesn't fail verify,
# but it won't pass the spec acceptance criterion either. Wave 1/2 add
# the missing examples/ dirs.
EXAMPLES := $(wildcard $(addsuffix /examples,$(addprefix .agent/skills/,$(SKILLS))))

.PHONY: verify list-skills help fixture-verify

help:
	@echo "Targets:"
	@echo "  make verify          Run every skill's examples/Makefile verify target"
	@echo "  make list-skills     Print the discovered skill list"
	@echo "  make fixture-verify  Build and run the _fixture skill (smoke test)"
	@echo "  make help            Show this help"

list-skills:
	@echo "Discovered skills (underscore-prefixed dirs are skipped):"
	@for s in $(SKILLS); do echo "  $$s"; done

verify:
	@echo "Verifying $(words $(EXAMPLES)) skill examples (REPO_ROOT=$(REPO_ROOT))..."
	@fail=0; \
	for ex in $(EXAMPLES); do \
	  echo "==> $$ex"; \
	  if ! $(MAKE) -C $$ex REPO_ROOT=$(REPO_ROOT) verify; then \
	    echo "  FAILED: $$ex"; \
	    fail=1; \
	  fi; \
	done; \
	if [ $$fail -ne 0 ]; then \
	  echo "VERIFY FAILED for at least one skill"; \
	  exit 1; \
	fi; \
	echo "VERIFY OK"

# Smoke-test entry: only the _fixture skill. We pass through to its
# Makefile with REPO_ROOT so it doesn't need to climb $(CURDIR).
fixture-verify:
	$(MAKE) -C .agent/skills/_fixture/examples REPO_ROOT=$(REPO_ROOT) verify
