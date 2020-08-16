`timescale 1ns / 1ps
module FPAddSub(
		clk,
		rst,
		a,
		b,
		operation,
		result,
		flags, 

        //8 bit adder exposed outside
	    fixed_pt_adder1_in_a,
	    fixed_pt_adder1_in_b,
	    fixed_pt_adder1_mode,
	    fixed_pt_adder1_cin,
	    fixed_pt_adder1_out,
	    fixed_pt_adder1_cout,

        //8 bit adder exposed outside
	    fixed_pt_adder2_in_a,
	    fixed_pt_adder2_in_b,
	    fixed_pt_adder2_mode,
	    fixed_pt_adder2_cin,
	    fixed_pt_adder2_out,
	    fixed_pt_adder2_cout,

        //24 bit adder exposed outside
	    fixed_pt_adder34_in_a,
	    fixed_pt_adder34_in_b,
	    fixed_pt_adder34_mode,
	    fixed_pt_adder34_cin,
	    fixed_pt_adder34_out,
	    fixed_pt_adder34_cout,

	    fixed_pt_adder5_in_a,
	    fixed_pt_adder5_in_b,
	    fixed_pt_adder5_mode,
	    fixed_pt_adder5_cin,
	    fixed_pt_adder5_out,
	    fixed_pt_adder5_cout
	);

// Clock and reset
	input clk ;										// Clock signal
	input rst ;										// Reset (active high, resets pipeline registers)
	
	// Input ports
	input [31:0] a ;								// Input A, a 32-bit floating point number
	input [31:0] b ;								// Input B, a 32-bit floating point number
	input operation ;								// Operation select signal
	
	// Output ports
	output [31:0] result ;						// Result of the operation
	output [4:0] flags ;							// Flags indicating exceptions according to IEEE754

	output [7:0] fixed_pt_adder1_in_a;
	output [7:0] fixed_pt_adder1_in_b;
	output       fixed_pt_adder1_mode;
	output       fixed_pt_adder1_cin;
	input  [7:0] fixed_pt_adder1_out;
	input        fixed_pt_adder1_cout;

	output [7:0] fixed_pt_adder2_in_a;
	output [7:0] fixed_pt_adder2_in_b;
	output       fixed_pt_adder2_mode;
	output       fixed_pt_adder2_cin;
	input  [7:0] fixed_pt_adder2_out;
	input        fixed_pt_adder2_cout;

	output [23:0] fixed_pt_adder34_in_a;
	output [23:0] fixed_pt_adder34_in_b;
	output        fixed_pt_adder34_mode;
	output        fixed_pt_adder34_cin;
	input  [23:0] fixed_pt_adder34_out;
	input         fixed_pt_adder34_cout;

	output [7:0] fixed_pt_adder5_in_a;
	output [7:0] fixed_pt_adder5_in_b;
	output       fixed_pt_adder5_mode;
	output       fixed_pt_adder5_cin;
	input  [7:0] fixed_pt_adder5_out;
	input        fixed_pt_adder5_cout;

	wire [68:0]pipe_1;
	wire [54:0]pipe_2;
	wire [45:0]pipe_3;

wire dummy;
assign dummy = clk | rst;

//internal module wires

//output ports
	wire Opout;
	wire Sa;
	wire Sb;
	wire MaxAB;
	wire [7:0] CExp;
	wire [4:0] Shift;
	wire [22:0] Mmax;
	wire [4:0] InputExc;
	wire [23:0] Mmin_3;

	wire [32:0] SumS_5 ;
	wire [4:0] Shift_1;							
	wire PSgn ;							
	wire Opr ;	
	
	wire [22:0] NormM ;				// Normalized mantissa
	wire [8:0] NormE ;					// Adjusted exponent
	wire ZeroSum ;						// Zero flag
	wire NegE ;							// Flag indicating negative exponent
	wire R ;								// Round bit
	wire S ;								// Final sticky bit
	wire FG ;

FPAddSub_a M1(a,b,operation,Opout,Sa,Sb,MaxAB,CExp,Shift,Mmax,InputExc,Mmin_3,
	    fixed_pt_adder1_in_a,
	    fixed_pt_adder1_in_b,
	    fixed_pt_adder1_mode,
	    fixed_pt_adder1_cin,
	    fixed_pt_adder1_out,
	    fixed_pt_adder1_cout,

	    fixed_pt_adder2_in_a,
	    fixed_pt_adder2_in_b,
	    fixed_pt_adder2_mode,
	    fixed_pt_adder2_cin,
	    fixed_pt_adder2_out,
	    fixed_pt_adder2_cout);

FpAddSub_b M2(pipe_1[51:29],pipe_1[23:0],pipe_1[67],pipe_1[66],pipe_1[65],pipe_1[68],SumS_5,Shift_1,PSgn,Opr,
	    fixed_pt_adder34_in_a,
	    fixed_pt_adder34_in_b,
	    fixed_pt_adder34_mode,
	    fixed_pt_adder34_cin,
	    fixed_pt_adder34_out,
	    fixed_pt_adder34_cout);

FPAddSub_c M3(pipe_2[54:22],pipe_2[21:17],pipe_2[16:9],NormM,NormE,ZeroSum,NegE,R,S,FG,
	    fixed_pt_adder5_in_a,
	    fixed_pt_adder5_in_b,
	    fixed_pt_adder5_mode,
	    fixed_pt_adder5_cin,
	    fixed_pt_adder5_out,
	    fixed_pt_adder5_cout);

FPAddSub_d M4(pipe_3[13],pipe_3[22:14],pipe_3[45:23],pipe_3[11],pipe_3[10],pipe_3[9],pipe_3[8],pipe_3[7],pipe_3[6],pipe_3[5],pipe_3[12],pipe_3[4:0],result,flags );


/*
pipe_1:
	[68] Opout;
	[67] Sa;
	[66] Sb;
	[65] MaxAB;
	[64:57] CExp;
	[56:52] Shift;
	[51:29] Mmax;
	[28:24] InputExc;
	[23:0] Mmin_3;	

*/

assign pipe_1 = {Opout,Sa,Sb,MaxAB,CExp,Shift,Mmax,InputExc,Mmin_3};

/*
pipe_2:
	[54:22]SumS_5;
	[21:17]Shift;
	[16:9]CExp;	
	[8]Sa;
	[7]Sb;
	[6]operation;
	[5]MaxAB;	
	[4:0]InputExc
*/

assign pipe_2 = {SumS_5,Shift_1,pipe_1[64:57], pipe_1[67], pipe_1[66], pipe_1[68], pipe_1[65], pipe_1[28:24] };

/*
pipe_3:
	[45:23] NormM ;				
	[22:14] NormE ;					
	[13]ZeroSum ;						
	[12]NegE ;							
	[11]R ;								
	[10]S ;								
	[9]FG ;
	[8]Sa;
	[7]Sb;
	[6]operation;
	[5]MaxAB;	
	[4:0]InputExc
*/

assign pipe_3 = {NormM,NormE,ZeroSum,NegE,R,S,FG, pipe_2[8], pipe_2[7], pipe_2[6], pipe_2[5], pipe_2[4:0] };


endmodule
`timescale 1ns / 1ps
// Prealign + Align + Shift 1 + Shift 2
module FPAddSub_a(
		A,
		B,
		operation,
		Opout,
		Sa,
		Sb,
		MaxAB,
		CExp,
		Shift,
		Mmax,
		InputExc,
		Mmin_3,
	    fixed_pt_adder1_in_a,
	    fixed_pt_adder1_in_b,
	    fixed_pt_adder1_mode,
	    fixed_pt_adder1_cin,
	    fixed_pt_adder1_out,
	    fixed_pt_adder1_cout,

	    fixed_pt_adder2_in_a,
	    fixed_pt_adder2_in_b,
	    fixed_pt_adder2_mode,
	    fixed_pt_adder2_cin,
	    fixed_pt_adder2_out,
	    fixed_pt_adder2_cout
	);
	
	// Input ports
	input [31:0] A ;										// Input A, a 32-bit floating point number
	input [31:0] B ;										// Input B, a 32-bit floating point number
	input operation ;
	
	//output ports
	output Opout;
	output Sa;
	output Sb;
	output MaxAB;
	output [7:0] CExp;
	output [4:0] Shift;
	output [22:0] Mmax;
	output [4:0] InputExc;
	output [23:0] Mmin_3;

	output [7:0] fixed_pt_adder1_in_a;
	output [7:0] fixed_pt_adder1_in_b;
	output       fixed_pt_adder1_mode;
	output       fixed_pt_adder1_cin;
	input  [7:0] fixed_pt_adder1_out;
	input        fixed_pt_adder1_cout;

	output [7:0] fixed_pt_adder2_in_a;
	output [7:0] fixed_pt_adder2_in_b;
	output       fixed_pt_adder2_mode;
	output       fixed_pt_adder2_cin;
	input  [7:0] fixed_pt_adder2_out;
	input        fixed_pt_adder2_cout;
							
	wire [9:0] ShiftDet ;							
	wire [30:0] Aout ;
	wire [30:0] Bout ;
	

	// Internal signals									// If signal is high...
	wire ANaN ;												// A is a NaN (Not-a-Number)
	wire BNaN ;												// B is a NaN
	wire AInf ;												// A is infinity
	wire BInf ;												// B is infinity
	wire [7:0] DAB ;										// ExpA - ExpB					
	wire [7:0] DBA ;										// ExpB - ExpA	
	
	assign ANaN = &(A[30:23]) & |(A[22:0]) ;		// All one exponent and not all zero mantissa - NaN
	assign BNaN = &(B[30:23]) & |(B[22:0]);		// All one exponent and not all zero mantissa - NaN
	assign AInf = &(A[30:23]) & ~|(A[22:0]) ;	// All one exponent and all zero mantissa - Infinity
	assign BInf = &(B[30:23]) & ~|(B[22:0]) ;	// All one exponent and all zero mantissa - Infinity
	
	// Put all flags into exception vector
	assign InputExc = {(ANaN | BNaN | AInf | BInf), ANaN, BNaN, AInf, BInf} ;
	
	//assign DAB = (A[30:23] - B[30:23]) ;
	//assign DBA = (B[30:23] - A[30:23]) ;
	//`ifndef SYNTHESIS_
  //assign DAB = (A[30:23] + ~(B[30:23]) + 1) ;
	//assign DBA = (B[30:23] + ~(A[30:23]) + 1) ;
  //`else
  //DW01_add #(8) u_add1(.A(A[30:23]), .B(~(B[30:23])), .CI(1'b1), .SUM(DAB), .CO());
  //DW01_add #(8) u_add2(.A(B[30:23]), .B(~(A[30:23])), .CI(1'b1), .SUM(DBA), .CO());
	//`endif
  // Sending addition inputs outside, doing the actual multiplication outside and then getting the sum back in

	wire DAB_cout;
	assign fixed_pt_adder1_in_a = A[30:23];
	assign fixed_pt_adder1_in_b = B[30:23];
	assign fixed_pt_adder1_mode = 1'b1; //subtractor
	assign fixed_pt_adder1_cin  = 1'b0;
	assign DAB = fixed_pt_adder1_out;
	assign DAB_cout = fixed_pt_adder1_cout;

	wire DBA_cout;
	assign fixed_pt_adder2_in_a = B[30:23];
	assign fixed_pt_adder2_in_b = A[30:23];
	assign fixed_pt_adder2_mode = 1'b1; //subtractor
	assign fixed_pt_adder2_cin  = 1'b0;
	assign DBA = fixed_pt_adder2_out;
	assign DBA_cout = fixed_pt_adder2_cout;
	
	assign Sa = A[31] ;									// A's sign bit
	assign Sb = B[31] ;									// B's sign	bit
	assign ShiftDet = {DBA[4:0], DAB[4:0]} ;		// Shift data
	assign Opout = operation ;
	assign Aout = A[30:0] ;
	assign Bout = B[30:0] ;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// Output ports
													// Number of steps to smaller mantissa shift right
	wire [22:0] Mmin_1 ;							// Smaller mantissa 
	
	// Internal signals
	//wire BOF ;										// Check for shifting overflow if B is larger
	//wire AOF ;										// Check for shifting overflow if A is larger
	
	assign MaxAB = (Aout[30:0] < Bout[30:0]) ;	
	//assign BOF = ShiftDet[9:5] < 25 ;		// Cannot shift more than 25 bits
	//assign AOF = ShiftDet[4:0] < 25 ;		// Cannot shift more than 25 bits
	
	// Determine final shift value
	//assign Shift = MaxAB ? (BOF ? ShiftDet[9:5] : 5'b11001) : (AOF ? ShiftDet[4:0] : 5'b11001) ;
	
	assign Shift = MaxAB ? ShiftDet[9:5] : ShiftDet[4:0] ;
	
	// Take out smaller mantissa and append shift space
	assign Mmin_1 = MaxAB ? Aout[22:0] : Bout[22:0] ; 
	
	// Take out larger mantissa	
	assign Mmax = MaxAB ? Bout[22:0]: Aout[22:0] ;	
	
	// Common exponent
	assign CExp = (MaxAB ? Bout[30:23] : Aout[30:23]) ;	

// Input ports
					// Smaller mantissa after 16|12|8|4 shift
	wire [2:0] Shift_1 ;						// Shift amount
	
	assign Shift_1 = Shift [4:2];

	wire [23:0] Mmin_2 ;						// The smaller mantissa
	
	// Internal signals
	reg	  [23:0]		Lvl1;
	reg	  [23:0]		Lvl2;
	wire    [47:0]    Stage1;	
	integer           i;                // Loop variable
	
	always @(*) begin						
		// Rotate by 16?
		Lvl1 <= Shift_1[2] ? {17'b00000000000000001, Mmin_1[22:16]} : {1'b1, Mmin_1}; 
	end
	
	assign Stage1 = {Lvl1, Lvl1};
	
	always @(*) begin    					// Rotate {0 | 4 | 8 | 12} bits
	  case (Shift_1[1:0])
			// Rotate by 0	
			2'b00:  Lvl2 <= Stage1[23:0];       			
			// Rotate by 4	
			2'b01:  begin for (i=0; i<=23; i=i+1) begin Lvl2[i] <= Stage1[i+4]; end /*Lvl2[23:19] <= 0;*/ end
			// Rotate by 8
			2'b10:  begin for (i=0; i<=23; i=i+1) begin Lvl2[i] <= Stage1[i+8]; end /*Lvl2[23:15] <= 0;*/ end
			// Rotate by 12	
			2'b11:  begin for (i=0; i<=23; i=i+1) begin Lvl2[i] <= Stage1[i+12]; end /*Lvl2[23:11] <= 0;*/ end
	  endcase
	end
	
	// Assign output to next shift stage
	assign Mmin_2 = Lvl2;
								// Smaller mantissa after 16|12|8|4 shift
	wire [1:0] Shift_2 ;						// Shift amount
	
	assign Shift_2 =Shift  [1:0] ;
					// The smaller mantissa
	
	// Internal Signal
	reg	  [23:0]		Lvl3;
	wire    [47:0]    Stage2;	
	integer           j;               // Loop variable
	
	assign Stage2 = {Mmin_2, Mmin_2};

	always @(*) begin    // Rotate {0 | 1 | 2 | 3} bits
	  case (Shift_2[1:0])
			// Rotate by 0
			2'b00:  Lvl3 <= Stage2[23:0];   
			// Rotate by 1
			2'b01:  begin for (j=0; j<=23; j=j+1)  begin Lvl3[j] <= Stage2[j+1]; end /*Lvl3[23] <= 0;*/ end 
			// Rotate by 2
			2'b10:  begin for (j=0; j<=23; j=j+1)  begin Lvl3[j] <= Stage2[j+2]; end /*Lvl3[23:22] <= 0;*/ end 
			// Rotate by 3
			2'b11:  begin for (j=0; j<=23; j=j+1)  begin Lvl3[j] <= Stage2[j+3]; end /*Lvl3[23:21] <= 0;*/ end 	  
	  endcase
	end
	
	// Assign output
	assign Mmin_3 = Lvl3;	

	
endmodule
`timescale 1ns / 1ps

module FpAddSub_b(
		Mmax,
		Mmin,
		Sa,
		Sb,
		MaxAB,
		OpMode,
		SumS_5,
		Shift,
		PSgn,
		Opr,

	    fixed_pt_adder34_in_a,
	    fixed_pt_adder34_in_b,
	    fixed_pt_adder34_mode,
	    fixed_pt_adder34_cin,
	    fixed_pt_adder34_out,
	    fixed_pt_adder34_cout
);
	input [22:0] Mmax ;					// The larger mantissa
	input [23:0] Mmin ;					// The smaller mantissa
	input Sa ;								// Sign bit of larger number
	input Sb ;								// Sign bit of smaller number
	input MaxAB ;							// Indicates the larger number (0/A, 1/B)
	input OpMode ;							// Operation to be performed (0/Add, 1/Sub)
	
	// Output ports
	wire [32:0] Sum ;	
						// Output ports
	output [32:0] SumS_5 ;					// Mantissa after 16|0 shift
	output [4:0] Shift ;					// Shift amount				// The result of the operation
	output PSgn ;							// The sign for the result
	output Opr ;							// The effective (performed) operation

	output [23:0] fixed_pt_adder34_in_a;
	output [23:0] fixed_pt_adder34_in_b;
	output        fixed_pt_adder34_mode;
	output        fixed_pt_adder34_cin;
	input  [23:0] fixed_pt_adder34_out;
	input         fixed_pt_adder34_cout;

	assign Opr = (OpMode^Sa^Sb); 		// Resolve sign to determine operation

	// Perform effective operation
	//Original code:
  //`ifndef SYNTHESIS_
	//assign Sum = (OpMode^Sa^Sb) ? ({1'b1, Mmax, 8'b00000000} - {Mmin, 8'b00000000}) : ({1'b1, Mmax, 8'b00000000} + {Mmin, 8'b00000000}) ;
	//`else
  //wire [32:0] sum;
  //wire [32:0] sub;
  //DW01_add #(32) u_add(.A({1'b1, Mmax, 8'b00000000}), .B({Mmin, 8'b00000000}), .CI(1'b0), .SUM(sum[31:0]), .CO(sum[32]));
  //DW01_sub #(32) u_sub(.A({1'b1, Mmax, 8'b00000000}), .B({Mmin, 8'b00000000}), .CI(1'b0), .DIFF(sub[31:0]), .CO(sub[32]));
	//assign Sum = (OpMode^Sa^Sb) ? (sub) : (sum) ;
  //`endif 
	//Rewritten:
	//  One side of the mux :  ( {1'b1, Mmax} - Mmin ) << 8'b0
	//  Other side          :  ( {1'b1, Mmax} + Mmin ) << 8'b0
    // Sending addition inputs outside, doing the actual multiplication outside and then getting the sum back in
	
	wire [23:0] Sum_sum;
	wire Sum_cout;
	assign fixed_pt_adder34_in_a = {1'b1, Mmax}; //24 bits
	assign fixed_pt_adder34_in_b = Mmin;  //24 bits
	assign fixed_pt_adder34_mode = Opr;
	assign fixed_pt_adder34_cin  = 1'b0;
	assign Sum_sum  = fixed_pt_adder34_out; // 24 bits
	assign Sum_cout = fixed_pt_adder34_cout;
  assign Sum = {Sum_cout, Sum_sum, 8'b0}; //Shifted left by 8 bits
	
	// Assign result sign
	assign PSgn = (MaxAB ? Sb : Sa) ;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

		// Determine normalization shift amount by finding leading nought
	assign Shift =  ( 
		Sum[32] ? 5'b00000 :	 
		Sum[31] ? 5'b00001 : 
		Sum[30] ? 5'b00010 : 
		Sum[29] ? 5'b00011 : 
		Sum[28] ? 5'b00100 : 
		Sum[27] ? 5'b00101 : 
		Sum[26] ? 5'b00110 : 
		Sum[25] ? 5'b00111 :
		Sum[24] ? 5'b01000 :
		Sum[23] ? 5'b01001 :
		Sum[22] ? 5'b01010 :
		Sum[21] ? 5'b01011 :
		Sum[20] ? 5'b01100 :
		Sum[19] ? 5'b01101 :
		Sum[18] ? 5'b01110 :
		Sum[17] ? 5'b01111 :
		Sum[16] ? 5'b10000 :
		Sum[15] ? 5'b10001 :
		Sum[14] ? 5'b10010 :
		Sum[13] ? 5'b10011 :
		Sum[12] ? 5'b10100 :
		Sum[11] ? 5'b10101 :
		Sum[10] ? 5'b10110 :
		Sum[9] ? 5'b10111 :
		Sum[8] ? 5'b11000 :
		Sum[7] ? 5'b11001 : 5'b11010
	);
	
	reg	  [32:0]		Lvl1;
	
	always @(*) begin
		// Rotate by 16?
		Lvl1 <= Shift[4] ? {Sum[16:0], 16'b0000000000000000} : Sum; 
	end
	
	// Assign outputs
	assign SumS_5 = Lvl1;	

endmodule



`timescale 1ns / 1ps

module FPAddSub_c(
		SumS_5,
		Shift,
		CExp,
		NormM,
		NormE,
		ZeroSum,
		NegE,
		R,
		S,
		FG,
	    fixed_pt_adder5_in_a,
	    fixed_pt_adder5_in_b,
	    fixed_pt_adder5_mode,
	    fixed_pt_adder5_cin,
	    fixed_pt_adder5_out,
	    fixed_pt_adder5_cout
	);
	
	// Input ports
	input [32:0] SumS_5 ;						// Smaller mantissa after 16|12|8|4 shift
	
	input [4:0] Shift ;						// Shift amount
	
// Input ports
	
	input [7:0] CExp ;
	

	// Output ports
	output [22:0] NormM ;				// Normalized mantissa
	output [8:0] NormE ;					// Adjusted exponent
	output ZeroSum ;						// Zero flag
	output NegE ;							// Flag indicating negative exponent
	output R ;								// Round bit
	output S ;								// Final sticky bit
	output FG ;

	output [7:0] fixed_pt_adder5_in_a;
	output [7:0] fixed_pt_adder5_in_b;
	output       fixed_pt_adder5_mode;
	output       fixed_pt_adder5_cin;
	input  [7:0] fixed_pt_adder5_out;
	input        fixed_pt_adder5_cout;

	wire [3:0]Shift_1;
	assign Shift_1 = Shift [3:0];
	// Output ports
	wire [32:0] SumS_7 ;						// The smaller mantissa
	
	reg	  [32:0]		Lvl2;
	wire    [65:0]    Stage1;	
	reg	  [32:0]		Lvl3;
	wire    [65:0]    Stage2;	
	integer           i;               	// Loop variable
	
	assign Stage1 = {SumS_5, SumS_5};

	always @(*) begin    					// Rotate {0 | 4 | 8 | 12} bits
	  case (Shift[3:2])
			// Rotate by 0
			2'b00: Lvl2 <= Stage1[32:0];       		
			// Rotate by 4
			2'b01: begin for (i=65; i>=33; i=i-1) begin Lvl2[i-33] <= Stage1[i-4]; end /*Lvl2[3:0] <= 0;*/ end
			// Rotate by 8
			2'b10: begin for (i=65; i>=33; i=i-1) begin Lvl2[i-33] <= Stage1[i-8]; end /*Lvl2[7:0] <= 0;*/ end
			// Rotate by 12
			2'b11: begin for (i=65; i>=33; i=i-1) begin Lvl2[i-33] <= Stage1[i-12]; end /*Lvl2[11:0] <= 0;*/ end
	  endcase
	end
	
	assign Stage2 = {Lvl2, Lvl2};

	always @(*) begin   				 		// Rotate {0 | 1 | 2 | 3} bits
	  case (Shift_1[1:0])
			// Rotate by 0
			2'b00:  Lvl3 <= Stage2[32:0];
			// Rotate by 1
			2'b01: begin for (i=65; i>=33; i=i-1) begin Lvl3[i-33] <= Stage2[i-1]; end /*Lvl3[0] <= 0;*/ end 
			// Rotate by 2
			2'b10: begin for (i=65; i>=33; i=i-1) begin Lvl3[i-33] <= Stage2[i-2]; end /*Lvl3[1:0] <= 0;*/ end
			// Rotate by 3
			2'b11: begin for (i=65; i>=33; i=i-1) begin Lvl3[i-33] <= Stage2[i-3]; end /*Lvl3[2:0] <= 0;*/ end
	  endcase
	end
	
	// Assign outputs
	assign SumS_7 = Lvl3;						// Take out smaller mantissa



	
	// Internal signals
	wire MSBShift ;						// Flag indicating that a second shift is needed
	wire [8:0] ExpOF ;					// MSB set in sum indicates overflow
	wire [8:0] ExpOK ;					// MSB not set, no adjustment
	
	// Calculate normalized exponent and mantissa, check for all-zero sum
	assign MSBShift = SumS_7[32] ;		// Check MSB in unnormalized sum
	assign ZeroSum = ~|SumS_7 ;			// Check for all zero sum
  //`ifndef SYNTHESIS_
	//assign ExpOK = CExp - Shift ;		// Adjust exponent for new normalized mantissa
  //`else
  //DW01_sub #(8) u_sub(.A(CExp), .B({3'b000, Shift}), .CI(1'b0), .DIFF(ExpOK[7:0]), .CO(ExpOK[8]));
  //`endif
    // Sending addition inputs outside, doing the actual multiplication outside and then getting the sum back in
	// This is 8bit + 5bit adder. We'll just use a 8bit + 8bit adder outside.

	wire ExpOK_cout;
	wire [7:0] ExpOK_out;
	assign fixed_pt_adder5_in_a = CExp;
	assign fixed_pt_adder5_in_b = {3'b0, Shift};
	assign fixed_pt_adder5_mode = 1'b1; //subtractor
	assign fixed_pt_adder5_cin  = 1'b0;
	assign ExpOK_out = fixed_pt_adder5_out;
	assign ExpOK_cout = fixed_pt_adder5_cout;
	assign ExpOK = {ExpOK_cout, ExpOK_out};
	
	assign NegE = ExpOK[8] ;			// Check for exponent overflow
  `ifndef SYNTHESIS_
	assign ExpOF = CExp - Shift + 1'b1 ;		// If MSB set, add one to exponent(x2)
  `else
  assign ExpOF = ExpOK + 1'b1;
  `endif
	assign NormE = MSBShift ? ExpOF : ExpOK ;			// Check for exponent overflow
	assign NormM = SumS_7[31:9] ;		// The new, normalized mantissa
	
	// Also need to compute sticky and round bits for the rounding stage
	assign FG = SumS_7[8] ; 
	assign R = SumS_7[7] ;
	assign S = |SumS_7[6:0] ;		
	
endmodule
`timescale 1ns / 1ps

module FPAddSub_d(
		ZeroSum,
		NormE,
		NormM,
		R,
		S,
		G,
		Sa,
		Sb,
		Ctrl,
		MaxAB,
		NegE,
		InputExc,
		P,
		Flags 
    );

	// Input ports
	input ZeroSum ;					// Sum is zero
	input [8:0] NormE ;				// Normalized exponent
	input [22:0] NormM ;				// Normalized mantissa
	input R ;							// Round bit
	input S ;							// Sticky bit
	input G ;
	input Sa ;							// A's sign bit
	input Sb ;							// B's sign bit
	input Ctrl ;						// Control bit (operation)
	input MaxAB ;
	

	input NegE ;						// Negative exponent?
	input [4:0] InputExc ;					// Exceptions in inputs A and B

	// Output ports
	output [31:0] P ;					// Final result
	output [4:0] Flags ;				// Exception flags
	
	// 
	wire [31:0] Z ;					// Final result
	wire EOF ;
	
	// Internal signals
	wire [23:0] RoundUpM ;			// Rounded up sum with room for overflow
	wire [22:0] RoundM ;				// The final rounded sum
	wire [8:0] RoundE ;				// Rounded exponent (note extra bit due to poential overflow	)
	wire RoundUp ;						// Flag indicating that the sum should be rounded up
	wire ExpAdd ;						// May have to add 1 to compensate for overflow 
	wire RoundOF ;						// Rounding overflow
	wire FSgn;
	// The cases where we need to round upwards (= adding one) in Round to nearest, tie to even
	assign RoundUp = (G & ((R | S) | NormM[0])) ;
	
	// Note that in the other cases (rounding down), the sum is already 'rounded'
	assign RoundUpM = (NormM + 1) ;								// The sum, rounded up by 1
	assign RoundM = (RoundUp ? RoundUpM[22:0] : NormM) ; 	// Compute final mantissa	
	assign RoundOF = RoundUp & RoundUpM[23] ; 				// Check for overflow when rounding up

	// Calculate post-rounding exponent
	assign ExpAdd = (RoundOF ? 1'b1 : 1'b0) ; 				// Add 1 to exponent to compensate for overflow
	assign RoundE = ZeroSum ? 8'b00000000 : (NormE + ExpAdd) ; 							// Final exponent

	// If zero, need to determine sign according to rounding
	assign FSgn = (ZeroSum & (Sa ^ Sb)) | (ZeroSum ? (Sa & Sb & ~Ctrl) : ((~MaxAB & Sa) | ((Ctrl ^ Sb) & (MaxAB | Sa)))) ;

	// Assign final result
	assign Z = {FSgn, RoundE[7:0], RoundM[22:0]} ;
	
	// Indicate exponent overflow
	assign EOF = RoundE[8];

/////////////////////////////////////////////////////////////////////////////////////////////////////////



	
	// Internal signals
	wire Overflow ;					// Overflow flag
	wire Underflow ;					// Underflow flag
	wire DivideByZero ;				// Divide-by-Zero flag (always 0 in Add/Sub)
	wire Invalid ;						// Invalid inputs or result
	wire Inexact ;						// Result is inexact because of rounding
	
	// Exception flags
	
	// Result is too big to be represented
	assign Overflow = EOF | InputExc[1] | InputExc[0] ;
	
	// Result is too small to be represented
	assign Underflow = NegE & (R | S);
	
	// Infinite result computed exactly from finite operands
	assign DivideByZero = &(Z[30:23]) & ~|(Z[30:23]) & ~InputExc[1] & ~InputExc[0];
	
	// Invalid inputs or operation
	assign Invalid = |(InputExc[4:2]) ;
	
	// Inexact answer due to rounding, overflow or underflow
	assign Inexact = (R | S) | Overflow | Underflow;
	
	// Put pieces together to form final result
	assign P = Z ;
	
	// Collect exception flags	
	assign Flags = {Overflow, Underflow, DivideByZero, Invalid, Inexact} ; 	
	
endmodule
