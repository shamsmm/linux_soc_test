module jtag_top;
    import jtag::*;

    jtag_state_t state = dut.state;

    localparam PERIOD = 5;
    //localparam TIMEOUT = 5000;


    bit tdo, tdo_en, tclk, tdi, tms, trst, clk, tclk_en;
    logic [31:0] drscan = 0;

    always_comb tclk = tclk_en ? clk : 0;

    dtm_jtag dut(.*);

    task read_dr(); // 32 bit read
        assert(state == RUN_TEST_IDLE);

        @(negedge clk);
        tms = 1;
        @(posedge clk); #1 assert(state == SELECT_DR_SCAN);

        @(negedge clk);
        tms = 0;
        @(posedge clk); #1 assert(state == CAPTURE_DR);

        @(negedge clk);
        tms = 0;
        @(posedge clk) #1 assert(state == SHIFT_DR);

        drscan = 0; // initialize to 0
        repeat(32) begin
            @(negedge clk);
            tdi = 0;
            tms = 0;

            @(posedge clk) #1 assert(state == SHIFT_DR);
            drscan = {tdo, drscan[31:1]};
        end

        @(negedge clk);
        tms = 1;
        @(posedge clk); #1 assert(state == EXIT1_DR);

        @(negedge clk);
        tms = 1;
        @(posedge clk); #1 assert(state == UPDATE_DR);

        @(negedge clk);
        tms = 0; // hold it at RUN_TEST_IDLE
        @(posedge clk); #1 assert(state == RUN_TEST_IDLE);
        #1;
    endtask

    task update_ir(logic [5:0] ir); // 32 bit read
            assert(state == RUN_TEST_IDLE);

            @(negedge clk);
            tms = 1;
            @(posedge clk); #1 assert(state == SELECT_DR_SCAN);

            @(negedge clk);
            tms = 1;
            @(posedge clk); #1 assert(state == SELECT_IR_SCAN);

            @(negedge clk);
            tms = 0;
            @(posedge clk); #1 assert(state == CAPTURE_IR);

            @(negedge clk);
            tms = 0;
            @(posedge clk); #1 assert(state == SHIFT_IR);

            // shift instruction
            for (int i = 0; i < 5; i++) begin
                @(negedge clk);
                tdi = ir[i];
                tms = 0;
                @(posedge clk); #1 assert(state == SHIFT_IR);
            end
            @(negedge clk);
            tdi = ir[5];
            tms = 1;
            @(posedge clk); #1 assert(state == EXIT1_IR);

            @(negedge clk);
            tms = 1;
            @(posedge clk); #1 assert(state == UPDATE_IR);

            @(negedge clk);
            tms = 0; // hold it at RUN_TEST_IDLE
            @(posedge clk); #1 assert(state == RUN_TEST_IDLE);
            #1;
        endtask


    initial begin
        // Release reset
        trst = 1;
        #1 trst = 0;
        #1 trst = 1;

        // start

        @(negedge clk);
        tclk_en = 1; // enable test clock always

        tms = 1; // consecutive for 5 times

        repeat(5) @(posedge clk);
        assert(state == TEST_LOGIC_RESET);

        @(negedge clk);
        tms = 0; // got to RUN_TEST_IDLE
        @(posedge clk);
        #1;

        // read IDCODE initially
        read_dr();
        assert(drscan === 32'h1BEEF001);

        // test ILLEGAL PATTERN
        update_ir(6'b101010);
        assert(dut.ir === 6'b101010);

        read_dr();
        assert(drscan === 32'h0);

        // test SAMPLE PATTERN
        update_ir(6'b0);
        assert(dut.ir === 6'b0);

        read_dr();
        assert(drscan === 32'h55555555);

        // finish
        $finish();
    end

    initial forever #PERIOD clk = !clk;
    //initial #TIMEOUT $finish;

    initial begin
        // dump everything
        $dumpfile("dumpfile.fst");
        $dumpvars(0, jtag_top);
    end
endmodule