tier := build-sim

# valid_ready_if.sv is a reference example; iverilog does not support
# interface port declarations in modules, so only the pipeline TB is run.
SRCS := pipeline.sv tb_pipeline.sv

TOP  := tb_pipeline

REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
