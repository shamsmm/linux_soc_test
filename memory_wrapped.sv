// two ports, 1 Read only, other read and write
module memory_wrapped #(parameter int unsigned N = 1024) (
    slave_bus_if.slave ibus,
    slave_bus_if.slave dbus,
    input bit clk
);

bit rerror, rerror2, werror;

assign ibus.bdone = 1'b1;
assign dbus.bdone = 1'b1;

memory #(N) wrapped_mem (
    .data(dbus.rdata),
    .data2(ibus.rdata),
    .rerror(rerror),
    .rerror2(rerror2),
    .werror(werror),
    .write_data(dbus.wdata),
    .tsize(dbus.tsize),
    .clk(clk),
    .write(dbus.ss && dbus.ttype == WRITE), // state changing
    .address(dbus.addr[$clog2(N) - 1:0]),
    .address2(ibus.addr[$clog2(N) - 1:0])
);

endmodule