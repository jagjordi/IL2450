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

//    property lengthToggle(int prt);
//        @(negedge gif.clk)
//        $changed(gif.O_length[prt]) |=> 
    
    property length0_prop(int prt);
        @(negedge gif.clk) disable iff (!gif.reset)
        $fell(gif.O_end[0]) |=> !gif.O_length[prt] until gif.O_req[prt];
    endproperty
    
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

    //GOP0_lengthToggle : assert property (lengthToggle(0));
    //GOP1_lengthToggle : assert property (lengthToggle(1));
    //GOP2_lengthToggle : assert property (lengthToggle(2));
    
    GOP0_length0 : assert property (length0_prop(0));
    GOP1_length0 : assert property (length0_prop(1));
    GOP2_length0 : assert property (length0_prop(2));

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
