tier := build-sim

SRCS := and_gate.sv tb_and_gate.sv
TOP  := tb_and_gate

# REPO_ROOT is supplied by the root Makefile when it recurses via `$(MAKE) -C`.
# For direct invocation, fall back to climbing four levels up:
# examples/ -> _fixture/ -> skills/ -> .agent/ -> repo-root.
REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
