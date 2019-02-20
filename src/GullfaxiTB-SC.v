// Gullfaxi TB - sanity check

program Gullfaxi_tb
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
    
    parameter nrPkts = 10;
    parameter invProbWaitCycle = 1;
    parameter minWaitForSend = 2;
    parameter maxWaitForSend = 10;
    parameter minWaitForGrant = 2;
    parameter maxWaitForGrant = 10;
    parameter maxCycles = 2000;

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
    
    Packet packets_to_send[$];
    Packet expected_packets[$];

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
        for (int i = 0; i < nrPkts; i++) begin
            Packet p;
            p  = new;
            p.randomize();
            packets_to_send.push_back(p);
            expected_packets.push_back(p);
        end
    end

    initial begin : GIP_driver
        Packet cp;
        ##10;
        ck.reset <= 1;
        ##20;
        while (!packets_to_send.size()) begin
            $display("Time:", $time, " Starting to send packet");
            cp = packets_to_send.pop_front();
            
            // wait for GIP to be able to accept packets
            while(!ck.I_ready) #1;
            
            // begin transaction
            ck.I_valid <= 1;
            ck.I_data[7:2] <= cp.length;
            ck.I_data[1:0] <= cp.port;
            ##1;

            for(int i=0;i<9;i++) begin
                ck.I_valid <= 1;
                ck.I_data <= i;
                ##1;
                if ($urandom_range(100) < 1/invProbWaitCycle) begin
                    ck.I_valid <= 0;
                    ##1;
                end
            end
            ck.I_data <= 9;
            ck.I_end <= 1;
            ##1;

            $display("Time:", $time, " Ending to send packet");
            ck.I_valid <= 0;
            ck.I_data <= 0;
            ck.I_end <= 0;

            // wait for a random number of cycles
            ##($urandom_range(maxWaitForSend, minWaitForSend));
        end
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
