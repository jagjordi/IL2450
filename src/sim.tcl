vlog -cover  bcs src/*.sv
vsim -voptargs=+acc -coverage work.Gullfaxi_tb_top
add wave -position insertpoint sim:/Gullfaxi_tb_top/gif/*
