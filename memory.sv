// two ports, 1 Read only, other read and write
module memory #(parameter int unsigned N = 1024) (
    output bit [31:0] data,
    output bit [31:0] data2,
    output bit rerror,
    output bit rerror2,
    output bit werror,
    input bit [31:0] write_data,
    input tsize_e tsize,
    input bit clk,
    input bit write,
    input bit [$clog2(N)-1:0] address,
    input bit [$clog2(N)-1:0] address2
);
    bit [7:0] mem[N];

    always_comb begin
        if (address2[1:0] == 2'b00)
            data2 = {mem[address2 + 3], mem[address2 + 2], mem[address2 + 1], mem[address2]};
        else
            rerror2 = 1;
    end

    always_comb begin
        rerror = 0;
        case(tsize)
            WORD: begin
                if (address[1:0] == 2'b00)
                    data = {mem[address + 3], mem[address + 2], mem[address + 1], mem[address]};
                else
                    rerror = 1;
            end
            HALFWORD: begin
                if (address[0] == 1'b0)
                    data = {{16{0}}, mem[address + 1], mem[address]};
                else
                    rerror = 1;
            end
            BYTE: begin
                data = {{24{0}}, mem[address]};
            end
        endcase
    end

    // Write
    always_ff @(posedge clk) begin
        if (write) begin
            case(tsize)
                WORD: begin
                    if (address[1:0] == 2'b00) begin
                        {mem[address + 3], mem[address + 2], mem[address + 1], mem[address]} <= write_data;
                        werror <= 0;
                    end else
                        werror <= 1;
                end
                HALFWORD: begin
                    if (address[0] == 1'b0) begin
                        {mem[address + 1], mem[address]} = write_data[15:0];
                        werror <= 0;
                    end else
                        werror <= 1;
                end
                BYTE: begin
                    mem[address] <= write_data[7:0];
                    werror <= 0;
                end
            endcase
        end
    end

endmodule