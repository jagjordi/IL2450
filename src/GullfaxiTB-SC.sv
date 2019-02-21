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
    
    parameter nrPkts = 100000;
    parameter invProbWaitCycle = 0.1;
    parameter minWaitForSend = 2;
    parameter maxWaitForSend = 10;
    parameter minWaitForGrant = 2;
    parameter maxWaitForGrant = 10;
    parameter maxCycles = 2000;
        
    typedef enum {A, F, N, S} Type_e;

    class Packet;
        rand Type_e pktType;
        rand bit [1:0] outPort;
        rand bit [5:0] length;
        rand bit [7:0] playload [];

        constraint c {
            pktType dist {A := 12.5, F := 37.5, N := 25, S := 25};
            if (pktType == A) {
                outPort dist {2'b01 := 90, 2'b10 := 10};
                length inside {2, 4, 6, 8, 10};
            } else if (pktType == F) {
                outPort dist {2'b01 := 90, 2'b10 := 10};
                length inside {3, 5, 7, 9, 11};
            } else if (pktType == N) {
                outPort inside {[0:2]};
                length dist {5 := 2, [6:12] := 1};
            } else {
                outPort inside {[1:2]};
                if (outPort == 1) length inside {[1:8]};
                if (outPort == 2) length inside {[1:10]};
            }
            solve pktType before outPort;
            solve outPort before length;
            solve length before playload;
        }

        function void post_randomize();
            this.playload = new[this.length];
            if (this.pktType == F) begin
                int size;
                bit [7:0] checksum;
                bit [7:0] pl;
                size  = this.playload.size();
                checksum = this.playload[0];
                for (int i = 1; i < size; i++) checksum = checksum ^ this.playload[i];
                this.playload[size] = checksum;
            end
        endfunction
    endclass
    
    Packet packets_to_send[$];
    Packet expected_packets[$];

    Type_e pktType;
    bit [5:0] length;
    bit [1:0] outPort;

    default clocking ck @(posedge clk);
        default input #100ps output #100ps; // reading and writing skew
        output reset;
        output I_valid;
        output I_data;
        output I_end;
        input I_ready;
        input O_start;
        input O_length;
        input O_data;
        input O_end;
        input O_req;
        output O_grant;
    endclocking

    covergroup Cov1;
        pktType_c: coverpoint pktType;
        length_c: coverpoint length {
            ignore_bins ig1 = {12, 13, 14, 15};
        }
        outPort_c: coverpoint outPort {
            ignore_bins ig1 = {3};
        }

        cross pktType_c, outPort_c {
            ignore_bins ig1 = binsof(pktType_c) intersect {A} &&
                              binsof(outPort_c) intersect {0};
            ignore_bins ig2 = binsof(pktType_c) intersect {F} &&
                              binsof(outPort_c) intersect {0};
            ignore_bins ig3 = binsof(pktType_c) intersect {S} &&
                              binsof(outPort_c) intersect {0};
        }
        cross pktType_c, length_c {
            ignore_bins ig1 = binsof(pktType_c) intersect {A} &&
                              binsof(length_c)  intersect {0, 1, 3, 5, 7, 9, 11, 12, 13, 14, 15};
            ignore_bins ig2 = binsof(pktType_c) intersect {F} &&
                              binsof(length_c)  intersect {0, 1, 2, 4, 6, 8, 10, 12, 13, 14, 15};
            ignore_bins ig3 = binsof(pktType_c) intersect {N} &&
                              binsof(length_c)  intersect {0, 1, 2, 3, 4, 13, 14, 15};
            ignore_bins ig4 = binsof(pktType_c) intersect {S} &&
                              binsof(length_c)  intersect {0, 11, 12, 13, 14, 15};
            }
        cross length_c, outPort_c;

        type_transitions: coverpoint pktType {
            bins t4_A = (A[*4]);
            bins t4_F = (F[*4]);
            bins t8_A = (A[*8]);
            bins t8_F = (F[*8]);
            bins tA_3F_A = (A => F[*3] => A);
            bins tA_6F_A = (A => F[*6] => A);
            // A followed by 6 any types?
            bins tA
        }
    endgroup
      
    initial begin : generate_queues
        Cov1 cov;
        cov = new();
        `TIMESTAMP("Generating packets\n");
        for (int i = 0; i < nrPkts; i++) begin
            Packet p, copy;
            p  = new;
            p.randomize();
            // copy values to get coverage analisis
            pktType = p.pktType;
            length = p.length;
            outPort = p.outPort;
            // put elements in queues
            copy = new p;
            packets_to_send.push_back(p);
            expected_packets.push_back(copy);
            cov.sample();
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
            `TIMESTAMP($sformatf("GIP: Begining the transaction to outPort %0d, length %0d", packet_to_send.outPort, packet_to_send.length));
            ck.I_valid <= 1;
            ck.I_data[7:2] <= packet_to_send.length;
            ck.I_data[1:0] <= packet_to_send.outPort;
            ##1;

            for(int i = 0; i < packet_to_send.length; i++) begin
                ck.I_valid <= 1;
                ck.I_data <= packet_to_send.playload[i];
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
                    if (port != expected_packet.outPort) $error("Expected port doesn't match");

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
