// Gullfaxi TB - sanity check

`define TIMESTAMP(msg) $display("Time: %0d: %s", $time, msg)

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
    parameter invProbWaitCycle = 0.1;
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
        `TIMESTAMP("Generating packets\n");
        for (int i = 0; i < nrPkts; i++) begin
            Packet p, copy;
            p  = new;
            p.randomize();
            copy = new p;
            packets_to_send.push_back(p);
            expected_packets.push_back(copy);
        end
    end

    initial begin : GIP_driver
        Packet packet_to_send;
        ##10;
        ck.reset <= 1;
        ##20;
        while (packets_to_send.size()) begin
            `TIMESTAMP("GIP: Starting to send packets");
            packet_to_send = packets_to_send.pop_front();
            
            // wait for GIP to be able to accept packets
            while(!ck.I_ready) #1;
            
            // begin transaction
            `TIMESTAMP($sformatf("GIP: Begining the transaction to port %0d, length %0d", packet_to_send.port, packet_to_send.length));
            ck.I_valid <= 1;
            ck.I_data[7:2] <= packet_to_send.length;
            ck.I_data[1:0] <= packet_to_send.port;
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

            `TIMESTAMP("GIP: Ending to send packets\n");
            ck.I_valid <= 0;
            ck.I_data <= 0;
            ck.I_end <= 0;

            // wait for a random number of cycles
            ##($urandom_range(maxWaitForSend, minWaitForSend));
        end
        ##100;
        //$finish();
    end

    genvar port;

    //generating three processes, each controls and takes care of one port
    for (port=0;port<3;port++) begin : generateLoop
        // Output port controller and checker   
        initial begin : GOPcontroller
            Packet expected_packet;
            ck.O_grant[port] <= 0;
            forever begin
                if (ck.O_req[port]) begin
                    bit [7:0] payloadVec [$];
                    expected_packet = expected_packets.pop_front();
                    `TIMESTAMP($sformatf("GOP: Out port: %0d; request went up, length %0d", port, ck.O_length[port]));

                    // wait random number of cycles befor granting transmission
                    ##($urandom_range(maxWaitForGrant, minWaitForGrant));
                    `TIMESTAMP($sformatf("GOP: Out port: %0d; sending grant", port));
                    ck.O_grant[port] <= 1;
                    // wait before sneding starts
                    while(!ck.O_start[port]) ##1;
                    ck.O_grant[port] <= 0;
                    `TIMESTAMP($sformatf("GOP: Out port: %0d; sending started", port));
                    // Check if expected values match
                    if (ck.O_length[port] != expected_packet.length) $error("Expectet packet length doesn't match");
                    if (port != expected_packet.port) $error("Expected port doesn't match");

                    while (!ck.O_end[port]) begin
                        payloadVec.push_front(ck.O_data[port]);
                        ##1;
                    end
                    payloadVec.push_front(ck.O_data[port]);
                    // print received data
                    `TIMESTAMP($sformatf("GOP: Out port : %0d; sending finished", port));

                    $display("    Gathered ", payloadVec.size(), " elements");
                    $display("    Payload is: ");
                    while(payloadVec.size()!=0)
                        $display("        ", payloadVec.pop_back());
                end
                ##1;
            end
        end
    end

    initial begin : halt_checker
        ##(maxCycles);
        $finish();
    end
endprogram