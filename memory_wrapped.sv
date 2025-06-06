// two ports, 1 Read only, other read and write
module memory_wrapped #(parameter int unsigned N = 1024) (
    slave_bus_if.slave ibus,
    slave_bus_if.slave dbus,
    input bit clk,
    input bit rst_n
);

bit rerror, rerror2, werror;

enum logic {AD, DO} state, next_state, state2, next_state2;

always_ff @(posedge clk, negedge rst_n)
    if (!rst_n) begin
        state2 <= AD;
    end else begin
        state2 <= next_state2;
    end

always_comb begin
    case(state2)
        AD: next_state2 = ibus.bstart ? DO : AD;
        DO: next_state2 = AD;
    endcase
end

always_comb begin
    ibus.bdone = 0;
    case(state2)
        AD: ibus.bdone = 0;
        DO: ibus.bdone = 1;
    endcase
end

always_ff @(posedge clk, negedge rst_n)
    if (!rst_n)
        state <= AD;
    else    
        state <= next_state;

always_comb begin
    case(state)
        AD: next_state = dbus.bstart ? DO : AD;
        DO: next_state = AD;
    endcase
end

always_comb begin
    dbus.bdone = 0;
    case(state)
        AD: dbus.bdone = 0;
        DO: dbus.bdone = 1;
    endcase
end


// registered address, need 
memory_word #(N) wrapped_mem (
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