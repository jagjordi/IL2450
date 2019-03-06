typedef enum {A, F, N, S} Type_e;

interface GullfaxiInterface(input bit clk);
    bit reset;
    logic I_valid;
    logic [7:0] I_data;
    logic I_end;
    logic I_ready;

    // 0 -> port 0, 1 -> port 1, 2 -> port 2
    logic [2:0] O_start;
    logic [2:0][5:0] O_length;
    logic [2:0][7:0] O_data;
    logic [2:0] O_end;
    logic [2:0] O_req;
    logic [2:0] O_grant;  

    clocking cb @(posedge clk);
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

    modport DUT (output I_ready, O_length, O_data, O_end, O_req, O_start,
                 input reset, I_data, I_end, O_grant);
endinterface
 
class Randomizer;
    int waitCycleProb;
    int minWaitForSend;
    int maxWaitForSend;
    int minWaitForGrant;
    int maxWaitForGrant;

    function new(input int waitCycleProb, minWaitForSend, maxWaitForSend, minWaitForGrant, maxWaitForGrant);
        this.waitCycleProb = waitCycleProb;
        this.minWaitForSend = minWaitForSend;
        this.maxWaitForSend = maxWaitForSend;
        this.minWaitForGrant = minWaitForGrant;
        this.maxWaitForGrant = maxWaitForGrant;
    endfunction

    function int grant();
        return $urandom_range(maxWaitForGrant, minWaitForGrant);
    endfunction

    function int send();
        return $urandom_range(maxWaitForSend, minWaitForSend);
    endfunction

    function int waitCycle();
        return $urandom_range(100) < waitCycleProb;
    endfunction
endclass

class Packet;
    rand Type_e pktType;
    rand bit [1:0] outPort;
    rand bit [5:0] length;
    rand bit [7:0] payload [];

    constraint pktType_c {
        pktType dist {A := 12.5, F := 37.5, N := 25, S := 25};
        
        solve pktType before outPort;
        solve outPort before length;
        solve length before payload;
    }
    constraint outPort_c {
        if (pktType == A) {
            outPort dist {2'b01 := 90, 2'b10 := 10};
        } else if (pktType == F) {
            outPort dist {2'b01 := 90, 2'b10 := 10};
        } else if (pktType == N) {
            outPort inside {[0:2]};
        } else {
            outPort inside {[1:2]};
        }
        solve pktType before outPort;
        solve outPort before length;
        solve length before payload;
    }
    constraint length_c {
        if (pktType == A) {
            length inside {2, 4, 6, 8, 10};
        } else if (pktType == F) {
            length inside {3, 5, 7, 9, 11};
        } else if (pktType == N) {
            length dist {5 := 2, [6:12] := 1};
        } else {
            if (outPort == 1) length inside {[1:8]};
            if (outPort == 2) length inside {[1:10]};
        }
        solve pktType before outPort;
        solve outPort before length;
        solve length before payload;
    }
    constraint payload_c {
        payload.size() == length;
        solve pktType before outPort;
        solve outPort before length;
        solve length before payload;
    }

    function void pre_randomize();
        payload = new[13];
    endfunction

    function void post_randomize();
        if (this.pktType == F) begin
            int size;
            bit [7:0] checksum;
            bit [7:0] pl;
            size  = this.payload.size();
            checksum = this.payload[0];
            for (int i = 1; i < size; i++) checksum = checksum ^ this.payload[i];
            this.payload[size] = checksum;
        end
    endfunction
endclass

class Generator;
    mailbox #(Packet) generator_checker_mbx;
    mailbox #(Packet) generator_driver_mbx;
    Type_e pktType;
    bit[5:0] length;
    bit[1:0] outPort;
    int nrPkts;

    function new (input mailbox #(Packet) generator_driver_mbx,
                  input mailbox #(Packet) generator_checker_mbx,
                  int nrPkts);
        this.generator_checker_mbx = generator_checker_mbx;
        this.generator_driver_mbx = generator_driver_mbx;
        this.nrPkts = nrPkts;
        this.pktCov = new;
    endfunction

    covergroup pktCov;
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
            bins t48N_A = (F[*4:8] => A);
            bins tAF_FA = (A, F => F, A);
            bins tAF_3N_S = (A, F => N[*3] => S);
            bins t10AF = (A,F[*10]);
        }
    endgroup
    
    task run ();
        Packet p;
        repeat (nrPkts) begin
            p = new;
            //p.randomize();
            //p.randomize() with  {pktType != S;};
            p.randomize() with  {outPort == 0;};
            //p.pktType_c.constraint_mode(0);
            //p.randomize() with {pktType dist {A := 25, F := 50, N := 10, S := 15};};
            //p.randomize() with {outPort inside {0, 2}; length > 5;};
            //p.randomize() with {if (pktType == N) outPort == 0;};
            //p.randomize() with {if (length < 4) outPort == 0;};
            //p.pktType_c.constraint_mode(0);
            //p.randomize() with {pktType dist {A := 5, F := 75, N := 10, S := 10};};
            pktType = p.pktType;
            length = p.length;
            outPort = p.outPort;
            pktCov.sample();
            generator_driver_mbx.put(p);
            generator_checker_mbx.put(p);
        end
    endtask 
endclass

class Driver;
    mailbox #(Packet) generator_driver_mbx;
    virtual GullfaxiInterface gif;
    int nrPkts;
    Randomizer rd;

    function new (input mailbox #(Packet) generator_driver_mbx,
                  virtual GullfaxiInterface gif,
                  int nrPkts,
                  Randomizer rd);
        this.generator_driver_mbx = generator_driver_mbx;
        this.gif = gif;
        this.nrPkts = nrPkts;
        this.rd = rd;
    endfunction

    task run ();
        Packet p;
        repeat (nrPkts) begin
            generator_driver_mbx.get(p);

            while(!gif.cb.I_ready) #1;
            
            // begin transaction
            gif.cb.I_valid <= 1;
            gif.cb.I_data[7:2] <= p.length;
            gif.cb.I_data[1:0] <= p.outPort;
            @(gif.cb);

            if (p.length == 1) begin
                gif.cb.I_valid <= 1;
                gif.cb.I_end <= 1;
                gif.cb.I_data <= p.payload[0];
                @(gif.cb);
            end
            else begin
                int i;
                gif.cb.I_valid <= 1;
                gif.cb.I_data <= p.payload[0];
                @(gif.cb);
                // header and first byte can't be halted
                i = 1;
                while (i < p.length) begin
                    if (rd.waitCycle()) begin
                        gif.cb.I_valid <= 0;
                        @(gif.cb);
                    end
                    else begin
                        gif.cb.I_valid <= 1;
                        gif.cb.I_data <= p.payload[i];
                        if (i == (p.length - 1)) gif.cb.I_end <= 1;
                        i++;
                        @(gif.cb);
                    end
                end
            end

            gif.cb.I_valid <= 0;
            gif.cb.I_data <= 0;
            gif.cb.I_end <= 0;

            // wait for a random number of cycles
            repeat (rd.send()) @(gif.cb);
        end
    endtask
endclass

class Checker;
    mailbox #(Packet) generator_checker_mbx;
    mailbox #(Packet) monitor_checker_mbx;
    int nrPkts;

    function new (input mailbox #(Packet) monitor_checker_mbx,
                  input mailbox #(Packet) generator_checker_mbx, 
                  int nrPkts);
        this.generator_checker_mbx = generator_checker_mbx;
        this.monitor_checker_mbx = monitor_checker_mbx;
        this.nrPkts = nrPkts;
    endfunction

    task run ();
        Packet expected, received;
        repeat (nrPkts) begin
            generator_checker_mbx.get(expected);
            monitor_checker_mbx.get(received);

            if (expected.length == received.length &&
                //expected.payload == received.payload &&
                expected.outPort == received.outPort)
                 $display("Packet received correcly");
            else $error("Packet received incorrectly");
        end
    endtask
endclass

class Monitor;
    mailbox #(Packet) monitor_checker_mbx;
    virtual GullfaxiInterface gif;
    bit [2:0] port;
    Randomizer rd;

    function new (input mailbox #(Packet) monitor_checker_mbx,
                  virtual GullfaxiInterface gif,
                  Randomizer rd);
        this.monitor_checker_mbx = monitor_checker_mbx;
        this.gif = gif;
        this.rd = rd;
        this.tranCov = new;
    endfunction

    covergroup tranCov @(negedge gif.clk);
        I_ready_c : coverpoint gif.cb.I_ready;
        O0_rec_c : coverpoint gif.cb.O_req[0];
        O1_rec_c : coverpoint gif.cb.O_req[1];
        O2_rec_c : coverpoint gif.cb.O_req[2];
        O0_start_c : coverpoint gif.cb.O_start[0];
        O1_start_c : coverpoint gif.cb.O_start[1];
        O2_start_c : coverpoint gif.cb.O_start[2];
        O0_end_c : coverpoint gif.cb.O_end[0];
        O1_end_c : coverpoint gif.cb.O_end[1];
        O2_end_c : coverpoint gif.cb.O_end[2];
     
        req0_req1: cross O0_rec_c, O1_rec_c {
            illegal_bins il1 = binsof(O0_rec_c) intersect {1} &&
                               binsof(O1_rec_c) intersect {1};
        }
        req1_req2: cross O1_rec_c, O2_rec_c {
            illegal_bins il2 = binsof(O1_rec_c) intersect {1} &&
                               binsof(O2_rec_c) intersect {1};
        }
        req0_req2: cross O0_rec_c, O2_rec_c {
            illegal_bins il3 = binsof(O0_rec_c) intersect {1} &&
                               binsof(O2_rec_c) intersect {1};
        }
                        
        start0_end0: cross O0_start_c, O0_end_c;
        start1_end1: cross O1_start_c, O1_end_c;
        start2_end2: cross O2_start_c, O2_end_c;

        ready_tran: coverpoint gif.cb.I_ready {
            bins t101 = (1 => 0 => 1);
            bins t1001 = (1 => 0 => 0 => 1);
            bins t10001 = (1 => 0 => 0 => 0 => 1);
            bins t10_4_12_1 = (1 => 0[*4:12] => 1);
            bins t100_one = (1[*100]);
            bins t100_zero = (0[*100]);
        }
    endgroup;

    task run (bit [2:0] port);
        Packet p;
        gif.cb.O_grant[port] <= 0;
        forever begin
            if (gif.cb.O_req[port]) begin
                bit [7:0] payloadVec [$];

                // wait random number of cycles befor granting transmission
                repeat (rd.grant()) @(gif.cb);
                gif.cb.O_grant[port] <= 1;

                // wait before sneding starts
                while(!gif.cb.O_start[port]) @(gif.cb);

                gif.cb.O_grant[port] <= 0;

                while (!gif.cb.O_end[port]) begin
                    payloadVec.push_front(gif.cb.O_data[port]);
                    @(gif.cb);
                end
                payloadVec.push_front(gif.cb.O_data[port]);

                p = new;
                p.outPort = port;
                p.length = payloadVec.size();
                
                monitor_checker_mbx.put(p);
            end
            @(gif.cb);
        end
    endtask
endclass
