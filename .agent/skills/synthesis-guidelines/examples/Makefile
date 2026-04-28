# synthesis-guidelines examples: SV files can be syntax-checked with iverilog
# Full synthesis requires Vivado or DC
tier := build-only

SRCS = pipelined_mult_add.sv

TOP  = pipelined_mult_add

REPO_ROOT ?= $(abspath $(CURDIR)/../../../../..)
include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
