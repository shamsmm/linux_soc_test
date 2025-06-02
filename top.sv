module top;

bit clk, rst_n;

master_bus_if dbus_if_core0(clk, rst_n);
master_bus_if ibus_if_core0(clk, rst_n);

slave_bus_if dbus_if_mem0(clk, rst_n);
slave_bus_if ibus_if_mem0(clk, rst_n);

rv_core core0(.ibus(ibus_if_core0), .dbus(dbus_if_core0));
memory mem0(.ibus(ibus_if_mem0), .dbus(dbus_if_mem0));

always_comb begin
    // default bus values
    dbus_if_core0.ic.rdata = 1'b0;
    dbus_if_core0.ic.berror = 1'b0;
    dbus_if_core0.ic.bdone = 1'b0;
    dbus_if_core0.ic.bgnt = dbus_if_core0.ic.breq; // always grant (no contention)

    dbus_if_mem0.ic.ss = 1'b0;
    //dbus_if_sram0.ic.ss = 1'b0;
    //dbus_if_uart0.ic.ss = 1'b0;

    // connect to bus
    dbus_if_mem0.ic.wdata = dbus_if_core0.ic.wdata;
    dbus_if_mem0.ic.addr = dbus_if_core0.ic.addr;
    dbus_if_mem0.ic.tsize = dbus_if_core0.ic.tsize;
    dbus_if_mem0.ic.bstart = dbus_if_core0.ic.bstart;

    // poor man's multiplexor
    case(dbus_if_core0.ic.addr[31:28])
        4'hF: begin
            dbus_if_core0.ic.bdone = bus_if_mem0.ic.bdone;
            dbus_if_core0.ic.rdata = bus_if_mem0.ic.rdata;
            dbus_if_mem0.ic.ss = 1'b1;
        end
        // other
    endcase
end

always_comb begin
    // default bus values
    ibus_if_core0.ic.rdata = 1'b0;
    ibus_if_core0.ic.berror = 1'b0;
    ibus_if_core0.ic.bdone = 1'b0;
    ibus_if_core0.ic.bgnt = ibus_if_core0.ic.breq; // always grant (no contention)

    ibus_if_mem0.ic.ss = 1'b0;

    // connect to bus
    ibus_if_mem0.ic.wdata = ibus_if_core0.ic.wdata;
    ibus_if_mem0.ic.addr = ibus_if_core0.ic.addr;
    ibus_if_mem0.ic.tsize = ibus_if_core0.ic.tsize;
    ibus_if_mem0.ic.bstart = ibus_if_core0.ic.bstart;

    // poor man's multiplexor
    case(ibus_if_core0.ic.addr[31:28])
        4'hF: begin
            ibus_if_core0.ic.bdone = ibus_if_mem0.ic.bdone;
            ibus_if_core0.ic.rdata = ibus_if_mem0.ic.rdata;
            ibus_if_mem0.ic.ss = 1'b1;
        end
        // crossbar
    endcase
end

initial begin
    $readmemh("tb/memory.txt", imem.mem, 0, 15);
end

endmodule