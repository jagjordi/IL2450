// Gullfaxi TB TOP module REL. 1

module Gullfaxi_tb_top();

   bit            clk;
   bit            reset;
   
   // single input port - DUT naming comventions
   bit            I0_valid;
   bit [7:0]      I0_data;
   bit            I0_end;
   bit            I0_ready;
   // output port 0 - DUT naming conventions
   bit            O0_start;
   bit [5:0]      O0_length;
   bit [7:0]      O0_data;
   bit            O0_end;
   bit            O0_req;
   bit            O0_grant;
   // output port 1 - DUT naming conventions
   bit            O1_start;
   bit [5:0]      O1_length;
   bit [7:0]      O1_data;
   bit            O1_end;
   bit            O1_req;
   bit            O1_grant;
   // output port 2 - DUT naming conventions
   bit            O2_start;
   bit [5:0]      O2_length;
   bit [7:0]      O2_data;
   bit            O2_end;
   bit            O2_req;
   bit            O2_grant;

   // input port - Testbench naming conventions
   bit            I_valid;
   bit [7:0]      I_data;
   bit            I_end;
   bit            I_ready;
   // output ports - Testbench naming conventions
   bit [2:0]      O_start;  // 0 -> port 0, 1 -> port 1, 2 -> port 2
   bit [2:0][5:0] O_length; // 0 -> port 0, 1 -> port 1, 2 -> port 2
   bit [2:0][7:0] O_data;   // 0 -> port 0, 1 -> port 1, 2 -> port 2
   bit [2:0]      O_end;    // 0 -> port 0, 1 -> port 1, 2 -> port 2
   bit [2:0]      O_req;    // 0 -> port 0, 1 -> port 1, 2 -> port 2
   bit [2:0]      O_grant;  // 0 -> port 0, 1 -> port 1, 2 -> port 2

   assign I0_valid = I_valid;
   assign I0_data  = I_data;
   assign I0_end   = I_end;
   assign I_ready  = I0_ready;
   
   assign O_start  [0]     = O0_start;
   assign O_length [0]     = O0_length;
   assign O_data   [0]     = O0_data;
   assign O_end    [0]     = O0_end;
   assign O_req    [0]     = O0_req;
   assign O0_grant         = O_grant[0];

   assign O_start  [1]     = O1_start;
   assign O_length [1]     = O1_length;
   assign O_data   [1]     = O1_data;
   assign O_end    [1]     = O1_end;
   assign O_req    [1]     = O1_req;
   assign O1_grant         = O_grant[1];
   
   assign O_start  [2]     = O2_start;
   assign O_length [2]     = O2_length;
   assign O_data   [2]     = O2_data;
   assign O_end    [2]     = O2_end;
   assign O_req    [2]     = O2_req;
   assign O2_grant         = O_grant[2];   
   
   // generation of clock
   initial begin
      clk <= 1;
      forever
        #500ps clk <= ~clk;
   end
   
   // instantiation of Gullfaxi
   Gullfaxi    Gullfaxi_Inst (.*);

   // instantiation of the Gullfaxi test program
   Gullfaxi_tb Gullfaxi_tb_Inst (.*);
    
endmodule
