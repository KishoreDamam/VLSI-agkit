module tb_and_gate;
    logic a, b, y;
    int errors = 0;

    and_gate dut (.a(a), .b(b), .y(y));

    initial begin
        // Truth-table sweep
        {a, b} = 2'b00; #1; if (y !== 1'b0) errors++;
        {a, b} = 2'b01; #1; if (y !== 1'b0) errors++;
        {a, b} = 2'b10; #1; if (y !== 1'b0) errors++;
        {a, b} = 2'b11; #1; if (y !== 1'b1) errors++;

        if (errors == 0)
            $display("PASS: and_gate truth table");
        else
            $fatal(1, "FAIL: and_gate had %0d errors", errors);
    end
endmodule
