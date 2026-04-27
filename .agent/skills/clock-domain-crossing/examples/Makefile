tier := build-sim

SRCS := sync_2ff.sv tb_sync_2ff.sv

TOP  := tb_sync_2ff

REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
