// axi_lite_scoreboard.sv -- AXI-Lite dual-FIFO scoreboard
//
// Demonstrates:
//   - Two uvm_tlm_analysis_fifo instances decoupling write rate from compare rate
//   - run_phase fork: separate threads drain expected and actual FIFOs
//   - check_phase: verifies no unmatched expected transactions remain
//   - convert2string() used in all error messages for readable diagnostics
//
// Wiring (done by the env in connect_phase):
//   ref_model.ap.connect(sb.expected_fifo.analysis_export)  -- reference model output
//   monitor.ap.connect(sb.actual_fifo.analysis_export)      -- DUT observation

`ifndef AXI_LITE_SCOREBOARD_SV
`define AXI_LITE_SCOREBOARD_SV

// Assumes axi_lite_agent.sv is compiled in the same fileset (provides axi_lite_seq_item)

class axi_lite_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi_lite_scoreboard)

    // Two independent FIFOs decouple write() (zero-time, from monitor) from
    // get() (blocking, in the compare loop). FIFOs are unbounded uvm_components.
    uvm_tlm_analysis_fifo #(axi_lite_seq_item) expected_fifo;
    uvm_tlm_analysis_fifo #(axi_lite_seq_item) actual_fifo;

    // Counters for final report
    int unsigned pass_count;
    int unsigned fail_count;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // build_phase: create both FIFOs.
    // uvm_tlm_analysis_fifo IS a uvm_component (has parent); new() is acceptable
    // because FIFO type overrides are never needed in practice.
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        expected_fifo = new("expected_fifo", this);
        actual_fifo   = new("actual_fifo",   this);
    endfunction

    // run_phase: two parallel blocking loops drain expected and actual streams.
    // The fork ensures neither stream blocks the other -- they are ordered by arrival.
    task run_phase(uvm_phase phase);
        fork
            drain_and_compare();
        join_none
        // Note: objection is NOT raised here; the test raises/drops it.
        // This scoreboard runs as a passive consumer until the phase ends.
    endtask

    // drain_and_compare: paired get() calls block until both streams have an item.
    // Assumes in-order matching: expected[0] matches actual[0], etc.
    task drain_and_compare();
        axi_lite_seq_item exp_item, act_item;
        forever begin
            // Block until an expected item is available
            expected_fifo.get(exp_item);
            // Block until the corresponding actual item is available
            actual_fifo.get(act_item);
            compare_items(exp_item, act_item);
        end
    endtask

    function void compare_items(axi_lite_seq_item exp_item,
                                axi_lite_seq_item act_item);
        // Check all relevant fields; use === for 4-state comparison (catches X/Z)
        if ((exp_item.addr !== act_item.addr) ||
            (exp_item.data !== act_item.data) ||
            (exp_item.we   !== act_item.we)) begin
            `uvm_error("SB_MISMATCH",
                $sformatf("EXPECTED: %s  |  ACTUAL: %s",
                          exp_item.convert2string(),
                          act_item.convert2string()))
            fail_count++;
        end else begin
            `uvm_info("SB_PASS",
                $sformatf("OK: %s", act_item.convert2string()), UVM_HIGH)
            pass_count++;
        end
    endfunction

    // check_phase: runs after run_phase drains.
    // Flag any expected transactions that were never matched by the DUT.
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        if (expected_fifo.size() != 0)
            `uvm_error("SB_LEFTOVER",
                $sformatf("%0d expected item(s) were never matched by DUT",
                          expected_fifo.size()))
        if (actual_fifo.size() != 0)
            `uvm_error("SB_EXTRA",
                $sformatf("%0d actual item(s) from DUT had no expected match",
                          actual_fifo.size()))
    endfunction

    // report_phase: print final pass/fail summary
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SB_SUMMARY",
            $sformatf("Scoreboard: PASS=%0d  FAIL=%0d", pass_count, fail_count),
            UVM_NONE)
        if (fail_count > 0)
            `uvm_error("SB_FAIL", "Test FAILED -- see MISMATCH messages above")
    endfunction

endclass

`endif // AXI_LITE_SCOREBOARD_SV
