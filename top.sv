module top;
    import jtag::*;

// simulation clock period and timeout
localparam PERIOD = 5;
localparam JTAG_PERIOD = PERIOD * 3.375; // simulates 1MHz to 18MHz for example
localparam TIMEOUT = 60000;

// master clk and master rst_n
bit clk, sysrst_n,rst_n;
assign rst_n = !ndmreset & sysrst_n;
// Debugging
bit tdo, tdo_en, tclk, tdi, tms, trst, tclk_en, tclk_gen;
assign tdo = tdo_en & dtm_tdo;
logic [33+7:0] drscan = 0;
always tclk = tclk_en ? tclk_gen : 0;
initial #2 forever #JTAG_PERIOD tclk_gen = ~tclk_gen;

// riscv32 core-0 master interfaces to I-bus and D-bus
master_bus_if dbus_if_core0(clk, rst_n);
master_bus_if dbus_if_dm0(clk, rst_n);
master_bus_if ibus_if_core0(clk, rst_n);

// dual port memory interface to I-bus and D-bus 
slave_bus_if dbus_if_mem0(clk, rst_n);
slave_bus_if ibus_if_mem0(clk, rst_n);

// flash rom interface (read only) to bus (I-bus)
slave_bus_if ibus_if_rom0(clk, rst_n);

// gpio memory mapped interface to bus (D-bus)
slave_bus_if dbus_if_gpio0(clk, rst_n);

// plic (D-bus)
slave_bus_if dbus_if_plic0(clk, rst_n);

// clit (D-bus)
slave_bus_if dbus_if_clit0(clk, rst_n);

// riscv32 core-0
logic irq_sw0, irq_timer0, running, halted, haltreq, resumereq, resethaltreq;

// debug signals
access_register_command_control_t dbg_arcc;
logic [31:0] dbg_rwrdata;
logic [31:0] dbg_regout;
rv_core #(.INITIAL_PC(32'h2000_0000)) core0(.dbg_arcc(dbg_arcc), .dbg_rwrdata(dbg_rwrdata), .dbg_regout(dbg_regout), .haltreq(haltreq), .resumereq(resumereq), .resethaltreq(resethaltreq), .ibus(ibus_if_core0), .dbus(dbus_if_core0), .clk(clk), .rst_n(rst_n), .irq_sw(irq_sw0), .irq_timer(irq_timer0), .halted(halted), .running(running));

// dual port memory
memory_wrapped mem0(.ibus(ibus_if_mem0), .dbus(dbus_if_mem0), .clk(clk), .rst_n(rst_n));

// rom single port memory
rom_wrapped rom0(.bus(ibus_if_rom0), .clk(clk), .rst_n(rst_n));

// gpio memory mapped
gpio_wrapped gpio0(.bus(dbus_if_gpio0), .clk(clk));

// clint
clint clint0(.bus(dbus_if_clit0), .clk(clk), .irq_sw(irq_sw0), .irq_timer(irq_timer0), .rst_n(rst_n));

// interconnect

dbus_interconnect dbus_ic(.*);
ibus_interconnect ibus_ic(.*);

// Debug

bit dmi_start;
logic [1:0] dmi_op;
logic [33:2] dmi_data_o, dmi_data_i;
logic [7+33:34] dmi_address;
logic dmi_finish;
logic dtm_tdo;
dtm_jtag debug_transport(.tdi(tdi), .trst(trst), .tms(tms), .tclk(tclk), .tdo(dtm_tdo), .tdo_en(tdo_en), .dmi_start(dmi_start), .dmi_op(dmi_op), .dmi_data_o(dmi_data_o), .dmi_address(dmi_address), .dmi_finish(dmi_finish), .dmi_data_i(dmi_data_i), .clk(clk));

logic ndmreset;
dm debug_module(.dbus(dbus_if_dm0), .dbg_arcc(dbg_arcc), .dbg_rwrdata(dbg_rwrdata), .dbg_regout(dbg_regout), .haltreq(haltreq), .resumereq(resumereq), .resethaltreq(resethaltreq), .halted(halted), .running(running), .clk(clk), .ndmreset(ndmreset), .dmi_start(dmi_start), .dmi_op(dmi_op), .dmi_data_o(dmi_data_o), .dmi_address(dmi_address), .dmi_finish(dmi_finish), .dmi_data_i(dmi_data_i));

// assertions and coverage
property dbus_access_valid;
    @(posedge clk)
    dbus_if_core0.bstart && !rst_n |-> |{dbus_if_mem0.ss, dbus_if_gpio0.ss};
endproperty

property ibus_access_valid;
    @(posedge clk)
    ibus_if_core0.bstart && !rst_n |-> |{ibus_if_mem0.ss, ibus_if_rom0.ss};
endproperty


//read_w: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == WORD);
//read_h: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == HALFWORD);
//read_b: cover property (@(posedge clk) dbus_if_mem0.ttype == READ && dbus_if_mem0.tsize == BYTE);
//write_w: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == WORD);
//write_h: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == HALFWORD);
//write_b: cover property (@(posedge clk) dbus_if_mem0.ttype == WRITE && dbus_if_mem0.tsize == BYTE);

assert property(dbus_access_valid) else $error("Accessing illegal D-bus address %h", dbus_if_core0.addr);
assert property(ibus_access_valid) else $error("Accessing illegal I-bus address %h", ibus_if_core0.addr);

initial forever #PERIOD clk = !clk;
initial #TIMEOUT $finish();

initial begin
    sysrst_n = 1;

    // reset
    #1;
    sysrst_n = 0;
    # 1;
    sysrst_n = 1;

    // JTAG
    // Release reset
    trst = 1;
    #1 trst = 0;
    #1 trst = 1;

    @(negedge clk);
    tclk_en = 1; // enable test clock always (not like real world but after CDC-ing inside the DTM this is no problem)

    // read IDCODE initially
    jtag_run_test_idle();
    read_dr32(32'hDEADBEEF, drscan[31:0]);
    assert(drscan[31:0] === 32'h1BEEF001);

    // HALT the processor
    update_ir(6'h11); // access DMI
    read_dr41({7'h10, 32'h80000001, 2'b10}, drscan);
    #1000;
    assert(halted);


    // Read dmstatus
    jtag_run_test_idle();
    update_ir(6'h11); // access DMI
    read_dr41({7'h11, 32'h00000000, 2'b1}, drscan);
    #100;
    read_dr41(41'b0, drscan); // JTAG to spit out read data
    #1000;


    // Write garbage to data0
    read_dr41({7'h04, 32'hDEADBEEF, 2'b10}, drscan);
    #50;
    assert(debug_module.data0 == 32'hDEADBEEF);
    // Read garbage to data0
    read_dr41({7'h04, 32'h0, 2'b01}, drscan);
    #5;
    read_dr41(41'h0, drscan);
    assert(drscan[33:2] == 32'hDEADBEEF);
    

    #200;
    // Read debug pc into data 0
    read_dr41({7'h17, {8'h0, 1'b0, 3'd2, 1'b0, 1'b0, 1'b1, 1'b0, 16'h07b1}, 2'd2}, drscan);
    #100;
    // read data0
    read_dr41({7'h04, 32'h00000000, 2'b1}, drscan);
    #100;
    read_dr41(41'b0, drscan); // JTAG to spit out read data of last transaction
    assert(drscan[33:2] == core0.dpc); // should be the PC that is stuck now


    // Resume processor
    jtag_run_test_idle();
    update_ir(6'h11); // access DMI
    read_dr41({7'h10, 32'h40000001, 2'b10}, drscan);
    #1000;
    assert(running);

    #50;

    // let's reset the whole system
    read_dr41({7'h10, 32'h00000003, 2'b10}, drscan); // ndmreset 1==0 => 1to0 so should PC become default.
    #50;
    assert(ibus_if_core0.addr == 32'h2000_0000);
    read_dr41({7'h10, 32'h0000001, 2'b10}, drscan); // ndmreset 0==1 => 0to1 should be back to normal.
    #50;
    assert(ibus_if_core0.addr != 32'h2000_0000); // TODO: maybe code flashed coincidently makes it go back to this addree, I assume not
end

    task jtag_run_test_idle();
        tms = 1; // consecutive for 5 times
        repeat(5) @(posedge tclk);
        assert(state == TEST_LOGIC_RESET);

        @(negedge tclk);
        tms = 0; // got to RUN_TEST_IDLE
        @(posedge tclk);
        #1;
    endtask

// JTAG
jtag_state_t state;
always_comb state = debug_transport.state;

    task read_dr32(input logic [31:0] write_data, output logic [31:0] output_data); // 32 bit read
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

        output_data = 0; // initialize to 0
        repeat(31) begin
            @(negedge tclk);
            tdi = write_data[0];
            write_data = write_data >> 1;
            tms = 0;

            @(posedge tclk) #1 assert(state == SHIFT_DR);
            output_data = {tdo, output_data[31:1]};
        end
        @(negedge tclk);
        tdi = write_data[0];
        write_data = write_data >> 1;
        tms = 1;

        output_data = {tdo, output_data[31:1]};
        @(posedge tclk); #1 assert(state == EXIT1_DR);

        @(negedge tclk);
        tms = 1;
        @(posedge tclk); #1 assert(state == UPDATE_DR);

        @(negedge tclk);
        tms = 0; // hold it at RUN_TEST_IDLE
        @(posedge tclk); #1 assert(state == RUN_TEST_IDLE);
        #1;
    endtask

    task read_dr41(input logic [40:0] write_data, output logic [40:0] output_data); // 41 bit read
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

        output_data = 0; // initialize to 0
        repeat(40) begin
            @(negedge tclk);
            tdi = write_data[0];
            write_data = write_data >> 1;
            tms = 0;

            @(posedge tclk) #1 assert(state == SHIFT_DR);
            output_data = {tdo, output_data[40:1]};
        end
        @(negedge tclk);
        tdi = write_data[0];
        write_data = write_data >> 1;
        tms = 1;

        output_data = {tdo, output_data[40:1]};
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
    // dump everything
    $dumpfile("dumpfile.fst");
    $dumpvars(0, top);

    // initialize ROM memory
    $readmemh("rom.mi", rom0.wrapped_mem.mem,0,250);

    // initialize RAM memory
    //$readmemh("memory.hex", mem0.wrapped_mem.mem,0,1000);
end

endmodule