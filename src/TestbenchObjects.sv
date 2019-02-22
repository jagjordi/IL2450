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
endinterface
 
class Packet;
    typedef enum {A, F, N, S} Type_e;
    rand Type_e pktType;
    rand bit [1:0] outPort;
    rand bit [5:0] length;
    rand bit [7:0] payload [];

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
    int nrPkts;

    function new (input mailbox #(Packet) generator_driver_mbx, generator_checker_mbx, nrPkts);
        this.generator_checker_mbx = generator_checker_mbx;
        this.generator_driver_mbx = generator_driver_mbx;
        this.nrPkts = nrPkts;
    endfunction

    task run ();
        Packet p;
        repeat (nrPkts) begin
            p = new;
            p.randomize;
            generator_driver_mbx.put(p);
            generator_checker_mbx.put(p);
        end
    endtask 
endclass

class Driver;
    mailbox #(Packet) generator_driver_mbx;
    GullfaxiInterface gif;
    int nrPkts;

    function new (input mailbox #(Packet) generator_driver_mbx, GullfaxiInterface gif, nrPkts);
        this.generator_driver_mbx = generator_driver_mbx;
        this.gif = gif;
        this.nrPkts = nrPkts;
    endfunction

    task run ();
        Packet p;
        repeat (nrPkts) begin
            p = generator_driver_mbx.get();

            while(!gif.cb.I_ready) #1;
            
            // begin transaction
            gif.cb.I_valid <= 1;
            gif.cb.I_data[7:2] <= packet_to_send.length;
            gif.cb.I_data[1:0] <= packet_to_send.outPort;
            ##1 (gif.cb);

            if (packet_to_send.length == 1) begin
                gif.cb.I_valid <= 1;
                gif.cb.I_end <= 1;
                gif.cb.I_data <= packet_to_send.payload[0];
                ##1 (gif.cb);
            end
            else begin
                int i;
                gif.cb.I_valid <= 1;
                gif.cb.I_data <= packet_to_send.payload[0];
                ##1 (gif.cb);
                // header and first byte can't be halted
                i = 1;
                while (i < packet_to_send.length) begin
                    if ($urandom_range(100) < 1/invProbWaitCycle) begin
                        gif.cb.I_valid <= 0;
                        ##1 (gif.cb);
                    end
                    else begin
                        gif.cb.I_valid <= 1;
                        gif.cb.I_data <= packet_to_send.payload[i];
                        if (i == (packet_to_send.length - 1)) gif.cb.I_end <= 1;
                        i++;
                        ##1 (gif.cb);
                    end
                end
            end

            `TIMESTAMP("GIP: Ending to send packets\n");
            gif.cb.I_valid <= 0;
            gif.cb.I_data <= 0;
            gif.cb.I_end <= 0;

            // wait for a random number of cycles
            ##($urandom_range(maxWaitForSend, minWaitForSend)) (gif.cb);
        end
    endtask
endclass

class Checker;
    mailbox #(Packet) generator_checker_mbx;
    mailbox #(Packet) monitor_checker_mbx;
    int nrPkts;

    function new (input mailbox #(Packet) monitor_checker_mbx, generator_checker_mbx, nrPkts);
        this.generator_checker_mbx = generator_checker_mbx;
        this.monitor_checker_mbx = monitor_checker_mbx;
        this.nrPkts = nrPkts;
    endfunction

    task run ();
        Packet expected, received;
        repeat (nrPkts) begin
            expected = generator_checker_mbx.get();
            received = monitor_checker_mbx.get();

            if (expected.length == received.length &&
                //expected.payload == received.payload &&
                expected.port == received.port)
                 $display("Packet received correcly");
            else $error("Packet received incorrectly");
        end
    endtask
endclass

class Monitor;
    mailbox #(Packet) monitor_checker_mbx;
    GullfaxiInterface gif;
    bit [2:0] port;

    function new (input mailbox #(Packet) monitor_checker_mbx, GullfaxiInterface gif, port);
        this.monitor_checker_mbx = monitor_checker_mbx;
        this.gif = gif;
        this.port = port;
    endfunction

    task run ();
        Packet p;
        gif.cb.O_grant[port] <= 0;
        forever begin
            if (gif.cb.O_req[port]) begin
                bit [7:0] payloadVec [$];

                // wait random number of cycles befor granting transmission
                ##($urandom_range(maxWaitForGrant, minWaitForGrant));
                gif.cb.O_grant[port] <= 1;

                // wait before sneding starts
                while(!gif.cb.O_start[port]) ##1;

                gif.cb.O_grant[port] <= 0;

                while (!gif.cb.O_end[port]) begin
                    payloadVec.push_front(gif.cb.O_data[port]);
                    ##1;
                end
                payloadVec.push_front(gif.cb.O_data[port]);

                p = new;
                p.port = port;
                p.length = payloadVec.size();
                
                monitor_checker_mbx.put(p);
            end
            ##1;
        end
    endtask
endclass

