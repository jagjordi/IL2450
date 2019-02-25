`include "GullfaxiTBObjects.sv"
module Gullfaxi_tb_top();
    bit            clk;
    
    // generation of clock
    initial begin
        clk <= 1;
        forever #500ps clk <= ~clk;
    end
    
    GullfaxiInterface gif(clk);
    Gullfaxi DUT(.clk(gif.clk),
                 .reset(gif.reset),
                 .I0_valid(gif.I_valid),
                 .I0_data(gif.I_data),
                 .I0_end(gif.I_end),
                 .I0_ready(gif.I_ready),
                 .O0_start(gif.O_start[0]),
                 .O0_length(gif.O_length[0]),
                 .O0_data(gif.O_data[0]),
                 .O0_end(gif.O_end[0]),
                 .O0_req(gif.O_req[0]),
                 .O0_grant(gif.O_grant[0]),
                 .O1_start(gif.O_start[1]),
                 .O1_length(gif.O_length[1]),
                 .O1_data(gif.O_data[1]),
                 .O1_end(gif.O_end[1]),
                 .O1_req(gif.O_req[1]),
                 .O1_grant(gif.O_grant[1]),
                 .O2_start(gif.O_start[2]),
                 .O2_length(gif.O_length[2]),
                 .O2_data(gif.O_data[2]),
                 .O2_end(gif.O_end[2]),
                 .O2_req(gif.O_req[2]),
                 .O2_grant(gif.O_grant[2]));
    Gullfaxi_tb TB(gif);
endmodule
