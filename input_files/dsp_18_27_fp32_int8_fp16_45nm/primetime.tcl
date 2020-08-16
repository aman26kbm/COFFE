set sh_enable_page_mode true 
set search_path /home/projects/ljohn/aarora1/cadence_gpdk/gsclib045_all_v4.4/lan/flow/t1u1/reference_libs/GPDK045/gsclib045_all_v4.4/gsclib045/timing/ 
set link_path "* fast_vdd1v0_basicCells.modif.db" 
read_verilog /home/projects/ljohn/aarora1/coffe2_aman/COFFE/output_files/dsp_18_27_fp32_int8_fp16_45nm/dsp_pnr/netlist.v 
set_case_analysis 0 mode[0]
set_case_analysis 0 mode[1]
set_case_analysis 0 mode[2]
set_case_analysis 0 mode_flopped_1
#set_false_path -through 
set_false_path -to fp16_top_mult_flopped_reg*
set_false_path -to mult_out_fp_flopped_1_*
set_false_path -to resulta_flopped_1_reg*
set_false_path -to negate_out_flopped_1_reg*
#set_false_path -from -to
link 
create_clock -period 3.0 clk 
read_parasitics -increment /home/projects/ljohn/aarora1/coffe2_aman/COFFE/output_files/dsp_18_27_fp32_int8_fp16_45nm/dsp_pnr/spef.spef 
report_timing > /home/projects/ljohn/aarora1/coffe2_aman/COFFE/output_files/dsp_18_27_fp32_int8_fp16_45nm/dsp_pt/timing.rpt 
quit 
