// Gullfaxi TB - sanity check

program Gullfaxi_tb
    #(
        parameter nrPkts = 10;
        parameter invProbWaitCycle = 1;
        parameter minWaitForSend = 2;
        parameter maxWaitForSend = 3;
        parameter minWaitForGrant = 2;
        parameter maxWaitForGrant = 3;
        parameter maxCycles = 25;
    )
    (
        input  bit            clk,
        output bit            reset,
        // single input port
        output bit            I_valid,
        output bit [7:0]      I_data,
        output bit            I_end,
        input  bit            I_ready,
        // output port 0
        input  bit [2:0]      O_start,
        input  bit [2:0][5:0] O_length,
        input  bit [2:0][7:0] O_data,
        input  bit [2:0]      O_end,
        input  bit [2:0]      O_req,
        output bit [2:0]      O_grant
    );

    class Packet;
        rand bit [1:0] port;
        rand bit [5:0] length;
        constraint c_port {
            port >= 0;
            port <= 2;
        }
        constraint c_length {
            length >= 1;
            length <= 12;
        }
    endclass
    
    default clocking ck @(posedge clk);
        default input #100ps output #100ps; // reading and writing skew
        output           reset;
        output           I_valid;
        output           I_data;
        output           I_end;
        input            I_ready;
        input            O_start;
        input            O_length;
        input            O_data;
        input            O_end;
        input            O_req;
        output           O_grant;
    endclocking
    
    initial begin : generate_queues
        Packet packets_to_send[$];
        Packet expected_packets[$];


    initial begin : GIP_driver
        ##(10);
        ck.reset      <= 1;
        ##(20);
        $display("Time:", $time, " Starting to send packet - length = 10 out port = 1");
        ck.I_valid    <= 1;
        ck.I_data     <= 8'b001010_01; //length 10, output port 1
        ##1;
        for(int i=0;i<9;i++) begin
            ck.I_data  <= i;
            ##1;
        end
        ck.I_data     <= 9;
        ck.I_end      <= 1;
        ##1;
        $display("Time:", $time, " Ending to send packet");
        ck.I_valid    <= 0;
        ck.I_data     <= 0;
        ck.I_end      <= 0;
        ##2;
        $display("Time:", $time, " Starting to send packet - length = 6, out port = 0");
        ck.I_valid    <= 1;
        ck.I_data     <= 8'b000110_00; //length 6, output port 0
        ##1;
        for(int i=0;i<5;i++) begin
            ck.I_data  <= i;
            ##1;
        end
        ck.I_data     <= 5;
        ck.I_end      <= 1;
        ##1;
        $display("Time:", $time, " Ending to send packet");
        ck.I_valid   <= 0;
        ck.I_data    <= 0;
        ck.I_end     <= 0;
        ##100;
        $finish();
    end

    genvar port;

    //generating three processes, each controls and takes care of one port
    for (port=0;port<3;port++) begin : generateLoop
        // Output port controller and checker   
        initial begin : GOPcontroller
            ck.O_grant[port] <= 0;
            forever begin
                if (ck.O_req[port]) begin
                    bit [7:0] payloadVec [$];
                    $display("Time:", $time, " Out port ", port, " : request went up, length ", ck.O_length[port]);
                    ##1;
                    $display("Time:", $time, " Out port ", port, " : sending grant");
                    ck.O_grant[port] <= 1;
                    while(!ck.O_start[port])
                        ##1;
                    ck.O_grant[port] <= 0;
                    $display("Time:", $time, " Out port ", port, " : sending started");
                    while (!ck.O_end[port]) begin
                        payloadVec.push_front(ck.O_data[port]);
                        ##1;
                    end
                    payloadVec.push_front(ck.O_data[port]);
                    $display("Time:", $time, " Out port ", port, " : sending finished");
                    $display("    Gathered ", payloadVec.size(), " elements");
                    $display("    Payload is: ");
                    while(payloadVec.size()!=0)
                        $display("        ", payloadVec.pop_back());
                end
                ##1;
            end
        end
    end
endprogram
