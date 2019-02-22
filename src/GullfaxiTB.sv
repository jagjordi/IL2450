`include "TestbenchObjects.sv"
program Gullfaxi_tb (GullfaxiInterface gif);

    parameter nrPkts = 100000;
    parameter invProbWaitCycle = 0.1;
    parameter minWaitForSend = 2;
    parameter maxWaitForSend = 10;
    parameter minWaitForGrant = 2;
    parameter maxWaitForGrant = 10;
    parameter maxCycles = nrPkts * 100;
        
    typedef enum {A, F, N, S} Type_e;

    initial begin
        mailbox #(Packet) generator_checker_mbx,
        mailbox #(Packet) generator_driver_mbx,
        mailbox #(Packet) monitor_checker_mbx
        
        Monitor monitor0, monitor1, monitor2;
        Generator generator;
        Checker chekr;
        Driver driver;

        monitor0 = new(monitor_checker_mbx, gif, 0);
        monitor1 = new(monitor_checker_mbx, gif, 1);
        monitor2 = new(monitor_checker_mbx, gif, 2);
        generator = new(generator_driver_mbx, generator_checker_mbx, nrPkts);
        chekr = new(monitor_checker_mbx, generator_checker_mbx, nrPkts);
        driver = new(generator_driver_mbx, gif, nrPkts);

        fork
            monitor0.start();
            monitor1.start();
            monitor2.start();
            generator.start();
            chekr.start();
            driver.start();
        join

        $display("Done!");
    end
endprogram
