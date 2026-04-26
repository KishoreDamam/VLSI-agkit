tier := build-sim

SRCS := and_gate.sv tb_and_gate.sv
TOP  := tb_and_gate

# REPO_ROOT is supplied by the root Makefile when it recurses into
# us via `$(MAKE) -C ...`. As a fallback for direct invocation,
# climb three levels up from this file (examples -> _fixture -> skills -> .agent -> repo? No: examples -> _fixture -> skills -> .agent. Then one more for repo).
# Actually: examples/ -> _fixture/ -> skills/ -> .agent/ -> repo-root = 4 levels.
REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
