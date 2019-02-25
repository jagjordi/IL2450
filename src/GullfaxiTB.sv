`include "GullfaxiTBObjects.sv"

program automatic Gullfaxi_tb (GullfaxiInterface gif);

    parameter nrPkts = 100000;
    parameter waitCycleProb = 10; // 10%
    parameter minWaitForSend = 2;
    parameter maxWaitForSend = 10;
    parameter minWaitForGrant = 2;
    parameter maxWaitForGrant = 10;
    parameter maxCycles = nrPkts * 100;
        
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
