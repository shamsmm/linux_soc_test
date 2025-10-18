module jtag_top;
    import jtag::*;

    jtag_state_t state;
    always_comb state = dut.state;

    localparam PERIOD = 5;
    //localparam TIMEOUT = 5000;

    // DMI
    bit dmi_start;
    bit dmi_finish;
    logic [1:0] dmi_op;
    logic [33:2] dmi_data_o;
    logic [33:2] dmi_data_i;
    logic [7+33:34] dmi_address;

    bit tdo, tdo_en, tclk, tdi, tms, trst, clk, tclk_en;
    logic [31:0] drscan = 0;

    always_comb tclk = tclk_en ? clk : 0;

    dtm_jtag dut(.*);

    task read_dr(); // 32 bit read
        assert(state == RUN_TEST_IDLE);

        @(negedge tclk);
        tms = 1;
        @(posedge tclk); #1 assert(state == SELECT_DR_SCAN);

        @(negedge tclk);
        tms = 0;
        @(posedge tclk); #1 assert(state == CAPTURE_DR);

        @(negedge tclk);
        tms = 0;
        @(posedge tclk) #1 assert(state == SHIFT_DR);

        drscan = 0; // initialize to 0
        repeat(32) begin
            @(negedge tclk);
            tdi = 0;
            tms = 0;

            @(posedge tclk) #1 assert(state == SHIFT_DR);
            drscan = {tdo, drscan[31:1]};
        end

        @(negedge tclk);
        tms = 1;
        @(posedge tclk); #1 assert(state == EXIT1_DR);

        @(negedge tclk);
        tms = 1;
        @(posedge tclk); #1 assert(state == UPDATE_DR);

        @(negedge tclk);
        tms = 0; // hold it at RUN_TEST_IDLE
        @(posedge tclk); #1 assert(state == RUN_TEST_IDLE);
        #1;
    endtask

    task update_ir(logic [5:0] ir); // 32 bit read
            assert(state == RUN_TEST_IDLE);

            @(negedge tclk);
            tms = 1;
            @(posedge tclk); #1 assert(state == SELECT_DR_SCAN);

            @(negedge tclk);
            tms = 1;
            @(posedge tclk); #1 assert(state == SELECT_IR_SCAN);

            @(negedge tclk);
            tms = 0;
            @(posedge tclk); #1 assert(state == CAPTURE_IR);

            @(negedge tclk);
            tms = 0;
            @(posedge tclk); #1 assert(state == SHIFT_IR);

            // shift instruction
            for (int i = 0; i < 5; i++) begin
                @(negedge tclk);
                tdi = ir[i];
                tms = 0;
                @(posedge tclk); #1 assert(state == SHIFT_IR);
            end
            @(negedge tclk);
            tdi = ir[5];
            tms = 1;
            @(posedge tclk); #1 assert(state == EXIT1_IR);

            @(negedge tclk);
            tms = 1;
            @(posedge tclk); #1 assert(state == UPDATE_IR);

            @(negedge tclk);
            tms = 0; // hold it at RUN_TEST_IDLE
            @(posedge tclk); #1 assert(state == RUN_TEST_IDLE);
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