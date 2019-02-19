//*******************************************************//
// Gullfaxi - REL 1                                      //
//                                                       //
// Prepared by: Jean-Michel Chabloz - chabloz@kth.se     //
//                                                       //
// Changelog:                                            //
// 2013-03-25: REL1 - Initial code - tested for sanity   //
//*******************************************************//

module Gullfaxi
  #(DEPTH     = 64,
    LOGDEPTH  = 6,
    MAXLENGTH = 12)
   (
    input  logic         clk,
    input  logic         reset,
    // single input port
    input  logic         I0_valid,
    input  logic [7:0]   I0_data,
    input  logic         I0_end,
    output logic         I0_ready,
    // output port 0
    output logic         O0_start,
    output logic [5:0]   O0_length,
    output logic [7:0]   O0_data,
    output logic         O0_end,
    output logic         O0_req,
    input  logic         O0_grant,
    // output port 1
    output logic         O1_start,
    output logic [5:0]   O1_length,
    output logic [7:0]   O1_data,
    output logic         O1_end,
    output logic         O1_req,
    input  logic         O1_grant,
    // output port 2
    output logic         O2_start,
    output logic [5:0]   O2_length,
    output logic [7:0]   O2_data,
    output logic         O2_end,
    output logic         O2_req,
    input  logic         O2_grant
    );
   
   // fifo signals
   logic [7:0]            fifoWrData;
   logic                  fifoWrite;
   logic [LOGDEPTH-1:0]   fifoWrPtr;
   logic [DEPTH-1:0][7:0] fifoData;
   logic [7:0]            fifoRdData;
   logic                  fifoRead;
   logic [LOGDEPTH-1:0]   fifoRdPtr;

   // number of elements in the fifo
   logic [LOGDEPTH:0]   nElems;   

   // write logic   
   logic [LOGDEPTH-1:0]   wrPtr;

   // read logic
   enum logic [1:0] {rdIdle, rdFirstWord, rdWaitForGrant, rdSend} rdState;
   logic [5:0]            rdCnt;   
   logic [LOGDEPTH-1:0]   rdPtr;
   logic [5:0]            length;
   logic [1:0]            outPort;    

   // keeping track of number of packets in the fifo
   logic                  wrotePkt;
   logic                  readPkt;
   logic [LOGDEPTH-2:0]   nPkts;
    
   // vector-form output ports for easier indexing
   
   logic [2:0]            O_start;
   logic [2:0][5:0]       O_length;
   logic [2:0][7:0]       O_data;
   logic [2:0]            O_end;
   logic [2:0]            O_req;
   logic [2:0]            O_grant;

   assign O0_start   = O_start[0];
   assign O0_length  = O_length[0];
   assign O0_data    = O_data[0];
   assign O0_end     = O_end[0];
   assign O0_req     = O_req[0];
   assign O_grant[0] = O0_grant;
   
   assign O1_start   = O_start[1];
   assign O1_length  = O_length[1];
   assign O1_data    = O_data[1];
   assign O1_end     = O_end[1];
   assign O1_req     = O_req[1];
   assign O_grant[1] = O1_grant;
   
   assign O2_start   = O_start[2];
   assign O2_length  = O_length[2];
   assign O2_data    = O_data[2];
   assign O2_end     = O_end[2];
   assign O2_req     = O_req[2];
   assign O_grant[2] = O2_grant;
    
  // write process
  always_ff @(posedge clk, negedge reset) begin
    if (reset==0) begin
      wrPtr          <= 0;
      fifoWrData     <= 0;
      fifoWrPtr      <= 0;
      fifoWrite      <= 0;
      wrotePkt       <= 0;
    end
    else begin // clk edge
      // start if default assignments
      wrPtr          <= wrPtr;
      fifoWrData     <= 0;
      fifoWrPtr      <= 0;
      fifoWrite      <= 0;
      wrotePkt       <= 0;
      // end of default assignments
      if (I0_valid) begin
        fifoWrData   <= I0_data;
        fifoWrPtr    <= wrPtr;
        fifoWrite    <= 1;
        wrPtr        <= wrPtr + 1;
        if (I0_end) begin
          wrotePkt   <= 1;
        end
      end
    end
  end

  // read process
  always_ff @(posedge clk, negedge reset) begin
    if (reset==0) begin
      rdPtr     <= 0;
      fifoRdPtr <= 0;
      fifoRead  <= 0;
      rdState   <= rdIdle;
      readPkt   <= 0;
      length    <= 0;
      outPort   <= 0;
      rdCnt     <= 0;
      O_req     <= 0;
      O_length  <= 0;
      O_data    <= 0;
      O_start   <= 0;
      O_end     <= 0;
    end
    else begin
      // start of default assignments
      rdPtr     <= rdPtr;
      fifoRdPtr <= 0;
      fifoRead  <= 0;
      rdState   <= rdState;
      readPkt   <= 0;
      length    <= length;
      outPort   <= outPort;
      rdCnt     <= rdCnt;
      O_req     <= 0;
      O_length  <= 0;
      O_data    <= 0;
      O_start   <= 0;
      O_end     <= 0;
      // end of default assignments
      if (rdState == rdIdle) begin
        if (nPkts > 0) begin
          rdState   <= rdFirstWord;
          fifoRdPtr <= rdPtr;
          fifoRead  <= 1;
          rdPtr     <= rdPtr + 1;
          readPkt   <= 1;          
        end
      end
      else if (rdState == rdFirstWord) begin
        rdState                   <= rdWaitForGrant;
        length                    <= fifoRdData[7:2];
        outPort                   <= fifoRdData[1:0];
        O_req[fifoRdData[1:0]]    <= 1;
        O_length[fifoRdData[1:0]] <= fifoRdData[7:2];
      end
      else if (rdState == rdWaitForGrant) begin
        O_req[outPort]    <= 1;
        O_length[outPort] <= length;
        if (O_grant[outPort]) begin
          rdState   <= rdSend;
          fifoRead  <= 1;
          fifoRdPtr <= rdPtr;
          rdPtr     <= rdPtr + 1;
          rdCnt     <= 0;
        end
      end
      else if (rdState == rdSend) begin
        O_length[outPort]  <= length;
        O_data[outPort]    <= fifoRdData;
        if (rdCnt==0) begin
          // first element goes out
          O_start[outPort] <= 1;
          fifoRead         <= 1;
          fifoRdPtr        <= rdPtr;
          rdPtr            <= rdPtr + 1;
          rdCnt            <= rdCnt + 1;
        end
        else if (rdCnt == length-1) begin
          // last element goes out
          O_end[outPort] <= 1;
          rdState        <= rdIdle;
        end
        else begin
          // middle element goes out
          fifoRead  <= 1;
          fifoRdPtr <= rdPtr;
          rdPtr     <= rdPtr + 1;
          rdCnt     <= rdCnt + 1;
        end
      end
    end
  end

  // keep track of the number of elements and packets in the fifo
  always_ff @(posedge clk, negedge reset) begin
    if (reset==0) begin
      nPkts  <= 0;
      nElems <= 0;
    end
    else begin
      // start of default assignments
      nPkts  <= nPkts;
      nElems <= nElems;
      // end of default assignments
      if (wrotePkt & !readPkt) begin
        nPkts <= nPkts + 1;
      end
      else if (!wrotePkt & readPkt) begin
        nPkts <= nPkts - 1;
      end
      if (fifoWrite & !fifoRead) begin
        nElems <= nElems + 1; 
      end
      else if (!fifoWrite & fifoRead) begin
        nElems <= nElems - 1;
      end
    end
  end
   
  // fifo write process
  always_ff @(posedge clk, negedge reset) begin
    if (reset==0) begin
      fifoData <= 0;
    end
    else begin
      // start of default assignments
      fifoData <= fifoData;
      // end of default assignments
      if (fifoWrite) begin
        fifoData[fifoWrPtr] <= fifoWrData;
      end
    end
  end

  // fifo read process
  always_comb begin
    if (fifoRead) begin
      fifoRdData <= fifoData[fifoRdPtr];
    end
  end

  assign I0_ready = (nElems <= DEPTH - MAXLENGTH);
   
endmodule
