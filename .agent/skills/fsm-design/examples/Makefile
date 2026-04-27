tier := build-sim

SRCS := memctl_fsm.sv tb_memctl_fsm.sv

TOP  := tb_memctl_fsm

REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
