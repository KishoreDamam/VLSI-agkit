tier := build-sim

SRCS := pipelined_alu/pipelined_alu.sv pipelined_alu/tb_pipelined_alu.sv

TOP  := tb_pipelined_alu

REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
