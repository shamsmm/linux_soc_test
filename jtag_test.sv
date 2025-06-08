module jtag_top;
    localparam PERIOD = 5;
    localparam TIMEOUT = 1500;


    bit tdo, tdo_en, tclk, tdi, tms, trst, clk, tclk_en;

    logic [31:0] drscan = 0;

    always_comb tclk = tclk_en ? clk : 0;

    dtm_jtag dut(.*);

    typedef enum logic [3:0] {
        TEST_LOGIC_RESET = 4'h0,
        RUN_TEST_IDLE    = 4'h1,
        SELECT_DR_SCAN   = 4'h2,
        CAPTURE_DR       = 4'h3,
        SHIFT_DR         = 4'h4,
        EXIT1_DR         = 4'h5,
        PAUSE_DR         = 4'h6,
        EXIT2_DR         = 4'h7,
        UPDATE_DR        = 4'h8,
        SELECT_IR_SCAN   = 4'h9,
        CAPTURE_IR       = 4'hA,
        SHIFT_IR         = 4'hB,
        EXIT1_IR         = 4'hC,
        PAUSE_IR         = 4'hD,
        EXIT2_IR         = 4'hE,
        UPDATE_IR        = 4'hF
    } jtag_state_t;

    initial begin
        // Release reset
        trst = 1;
        #1 trst = 0;
        #1 trst = 1;

        // start

        @(negedge clk);
        tclk_en = 1;
        tms = 1;

        repeat(5) @(posedge clk);
        assert(dut.state == TEST_LOGIC_RESET);

        // read IDCODE
        tms = 0;
        @(posedge clk); #1 assert(dut.state == RUN_TEST_IDLE);
        tms = 1;
        @(posedge clk); #1 assert(dut.state == SELECT_DR_SCAN);
        tms = 0;    
        @(posedge clk); #1 assert(dut.state == CAPTURE_DR);
        tms = 0;
        @(posedge clk) #1 assert(dut.state == SHIFT_DR);

        repeat(32) begin
            tms = 0;
            @(posedge clk) #1 assert(dut.state == SHIFT_DR);
            drscan = {tdo, drscan[31:1]};
        end

        tms = 1;
        @(posedge clk); #1 assert(dut.state == EXIT1_DR);

        // test bypass

        repeat(10) @(posedge clk);
        tms = 0;
        @(posedge clk); #1 assert(dut.state == RUN_TEST_IDLE);
        tms = 1;
        @(posedge clk); #1 assert(dut.state == SELECT_DR_SCAN);
        tms = 1;
        @(posedge clk); #1 assert(dut.state == SELECT_IR_SCAN);
        tms = 0;
        @(posedge clk); #1 assert(dut.state == CAPTURE_IR);

        repeat(6) begin
            tms = 0;
            tdi = 1; // all 1s for BYPASS
            @(posedge clk); #1 assert(dut.state == SHIFT_IR);
        end

        tms = 1;
        @(posedge clk); #1 assert(dut.state == EXIT1_IR);

        tms = 1;
        @(posedge clk); #1 assert(dut.state == UPDATE_IR);

        tms = 1;
        @(posedge clk); #1 assert(dut.state == SELECT_DR_SCAN);
        
        tms = 0;    
        @(posedge clk); #1 assert(dut.state == CAPTURE_DR);

        tms = 0;
        @(posedge clk) #1 assert(dut.state == SHIFT_DR);

        tms = 0;
        tdi = 1;
        @(posedge clk) #1 assert(dut.state == SHIFT_DR);
        drscan = {tdo, drscan[31:1]};

        repeat(31) begin
            tms = 0;
            tdi = 0;
            @(posedge clk) #1 assert(dut.state == SHIFT_DR);
            drscan = {tdo, drscan[31:1]};
        end

        tms = 1;
    end

    initial forever #PERIOD clk = !clk;
    initial #TIMEOUT $finish;

    initial begin
        // dump everything
        $dumpfile("dumpfile.fst");
        $dumpvars(0, jtag_top);
    end
endmodule