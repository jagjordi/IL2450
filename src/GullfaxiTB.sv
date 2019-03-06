`include "GullfaxiTBObjects.sv"

program automatic Gullfaxi_tb (GullfaxiInterface gif);
    parameter nrPkts = 100000;
    parameter waitCycleProb = 10; // 10%
    parameter minWaitForSend = 2;
    parameter maxWaitForSend = 10;
    parameter minWaitForGrant = 2;
    parameter maxWaitForGrant = 10;
    parameter maxCycles = nrPkts * 100;
    
    sequence start1_seq(int prt);
        gif.O_grant[prt] ##2 gif.O_start[prt];
    endsequence

    property start1_prop(int prt);
        @(negedge gif.clk) 
        $rose(gif.O_grant[prt]) |-> start1_seq(prt);
    endproperty

    sequence start0_seq(int prt);
        !gif.O_grant[prt] ##2 !gif.O_start[prt];
    endsequence

    property start0_prop(int prt);
        @(negedge gif.clk)
        !gif.O_grant[prt] |-> start0_seq(prt);
    endproperty

    property endOutOfTran_prop(int prt);
        @(negedge gif.clk)
        gif.O_end[prt] |=> !gif.O_end[prt] until gif.O_start[prt];
    endproperty

    property reqNoFall_prop(int prt);
        @(negedge gif.clk) disable iff (!gif.reset)
        $fell(gif.O_req[prt]) |-> gif.O_start[prt];
    endproperty

    property reqFall_prop(int prt);
        @(negedge gif.clk)
        gif.O_start[prt] |=> gif.O_req[prt] until !gif.O_end[prt];
    endproperty

    property lengthToggle(int prt);
        @(negedge gif.clk) disable iff (!gif.reset)
        $changed(gif.O_length[prt]) |-> (gif.O_req[prt]) or ($past(gif.O_end[prt], 1));
    endproperty
        
    property length0_prop(int prt);
        @(negedge gif.clk) disable iff (!gif.reset)
        $fell(gif.O_end[prt]) |=> !gif.O_length[prt] until gif.O_req[prt];
    endproperty

    property endDuringTran_prop(int prt);
        gif.O_start[prt] |=> ((gif.O_length[prt] == 1) && (gif.O_end[prt])) || ((gif.O_length != 1) && (!gif.O_end[prt]));//##(/*gif.O_length[prt] - 1*/1) gif.O_end[prt]));
    endproperty
    
    sequence startOfPacket_seq;
        (!gif.reset ##1 gif.reset ##[0:$] gif.I_valid ) or (gif.I_end ##[2:$] gif.I_valid);
    endsequence
    
    property noWaitCycleAfterHeader_prop;
        @(negedge gif.clk) disable iff (!gif.reset)
        startOfPacket_seq |-> gif.I_valid;
    endproperty

    property noStartIfNotReady_prop;
        @(negedge gif.clk) disable iff (!gif.reset)
        startOfPacket_seq |-> $past(gif.I_ready, 1);
    endproperty

    property headerPortCheck;
        @(negedge gif.clk) disable iff (!gif.reset)
        startOfPacket_seq |-> gif.I_data[1:0] != 2'b11;
    endproperty

    property headerLengthCheck;
        @(negedge gif.clk) disable iff (!gif.reset)
        startOfPacket_seq |-> ((gif.I_data[7:2] >= 6'b1) and (gif.I_data[7:2] <= 6'b1100));
    endproperty
    
    property intraPacketDelay; 
        @(negedge gif.clk) disable iff (!gif.reset)
        gif.I_end |=> !gif.I_valid ##1 !gif.I_valid;
    endproperty
    
    property GIP_endOutOfTran_prop;
        @(negedge gif.clk) disable iff (!gif.reset)
        gif.I_end |=> !gif.I_end until gif.I_valid;
    endproperty

    //used to check sequence works
    //assert property (@(negedge gif.clk) startOfPacket_seq(0) |-> 0) else $info("sending header");

    GOP0_start1: assert property (start1_prop(0));
    GOP1_start1: assert property (start1_prop(1));
    GOP2_start1: assert property (start1_prop(2));
        
    GOP0_start0: assert property (start0_prop(0));
    GOP1_start0: assert property (start0_prop(1));
    GOP2_start0: assert property (start0_prop(2));
   
    GOP0_endOutOfTran: assert property (endOutOfTran_prop(0));
    GOP1_endOutOfTran: assert property (endOutOfTran_prop(1));
    GOP2_endOutOfTran: assert property (endOutOfTran_prop(2));
    
    GOP0_reqNoFall: assert property (reqNoFall_prop(0));
    GOP1_reqNoFall: assert property (reqNoFall_prop(1));
    GOP2_reqNoFall: assert property (reqNoFall_prop(2));
    
    GOP0_reqFall: assert property (reqFall_prop(0));
    GOP1_reqFall: assert property (reqFall_prop(1));
    GOP2_reqFall: assert property (reqFall_prop(2));

    GOP0_lengthToggle : assert property (lengthToggle(0));
    GOP1_lengthToggle : assert property (lengthToggle(1));
    GOP2_lengthToggle : assert property (lengthToggle(2));
    
    GOP0_length0 : assert property (length0_prop(0));
    GOP1_length0 : assert property (length0_prop(1));
    GOP2_length0 : assert property (length0_prop(2));
    
//    GOP0_endDuringTran : assert property (endDuringTran_prop(0));
//    GOP1_endDuringTran : assert property (endDuringTran_prop(1));
//    GOP2_endDuringTran : assert property (endDuringTran_prop(2));

    GIP_noWaitCycleAfterHeader : assert property (noWaitCycleAfterHeader_prop);
    GIP_noStartIfNotReady : assert property (noStartIfNotReady_prop);
    GIP_headerLengthCheck : assert property (headerLengthCheck);
    GIP_intraPacketDelay : assert property (intraPacketDelay);
    GIP_endOutOfTran : assert property (GIP_endOutOfTran_prop);

    initial begin
        mailbox #(Packet) generator_checker_mbx;
        mailbox #(Packet) generator_driver_mbx;
        mailbox #(Packet) monitor_checker_mbx;
        
        Monitor monitor;
        Generator generator;
        Checker chekr;
        Driver driver;
        Randomizer rd;
        
        generator_driver_mbx = new();
        generator_checker_mbx = new();
        monitor_checker_mbx = new();

        rd = new(waitCycleProb, minWaitForSend, maxWaitForSend, minWaitForGrant, maxWaitForGrant);
        monitor = new(monitor_checker_mbx, gif, rd);
        generator = new(generator_driver_mbx, generator_checker_mbx, nrPkts);
        chekr = new(monitor_checker_mbx, generator_checker_mbx, nrPkts);
        driver = new(generator_driver_mbx, gif, nrPkts, rd);

        gif.cb.reset <= 0;
        gif.cb.I_valid <= 0;
        gif.cb.I_data <= 0;
        gif.cb.I_end <= 0;
        gif.cb.O_grant <= 0;
        repeat(10) @(gif.cb);
        gif.cb.reset <= 1;
        repeat(10) @(gif.cb);

        fork
            monitor.run(0);
            monitor.run(1);
            monitor.run(2);
            generator.run();
            chekr.run();
            driver.run();
        join

        $display("Done!");
    end
endprogram
