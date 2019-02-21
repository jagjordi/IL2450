vlog src/*.sv
vsim -voptargs=+acc work.Gullfaxi_tb_top
add wave -position insertpoint sim:/Gullfaxi_tb_top/*
run
