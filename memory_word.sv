// two ports, 1 Read only, other read and write
module memory_word #(parameter int unsigned N = 1024) (
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
    localparam upper = $clog2(N) - 1;
    bit [31:0] mem[N / 4];

    logic [$clog2(N)-1:0] address_registered;

    always_ff @(posedge clk)
        address_registered <= address;

    always_comb begin
        data2 = 0;
        rerror2 = 1'b0;

        if (address2[1:0] == 2'b00)
            data2 = mem[address2[$clog2(N)-1:2]];
        else
            rerror2 = 1'b1;
    end

    always_comb begin
        data = 0;
        rerror = 0;

        case(tsize)
            WORD: begin
                if (address_registered[1:0] == 2'b00)
                    data = mem[address_registered[upper:2]];
                else
                    rerror = 1;
            end
            HALFWORD: begin
                if (address_registered[0] == 1'b0)
                    data = address_registered[1] ? {16'b0, mem[address_registered[upper:2]][31:16]} : {16'b0, mem[address_registered[upper:2]][15:0]};
                else
                    rerror = 1;
            end
            BYTE: begin
                case(address_registered[1:0])
                2'b00: data = {24'b0, mem[address_registered[upper:2]][7:0]};
                2'b01: data = {24'b0, mem[address_registered[upper:2]][15:8]};
                2'b10: data = {24'b0, mem[address_registered[upper:2]][23:16]};
                2'b11: data = {24'b0, mem[address_registered[upper:2]][31:24]};
            endcase
            end
            default: rerror = 1;
        endcase
    end

    // Write
    always_ff @(posedge clk) begin
        if (write) begin
            mem[address_registered[upper:2]] <= write_data;
        end
    end

endmodule