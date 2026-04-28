tier := tool-output

# No simulation sources needed for constraint files.
# tier=tool-output: tools.mk will print a manual-review message and exit 0.

REPO_ROOT ?= $(abspath $(CURDIR)/../../../..)

include $(REPO_ROOT)/tools.mk

.PHONY: verify clean

verify: $(SIM_VERIFY_TARGET)

clean:
	$(SIM_CLEAN)
