module multi_cycle(SW,LEDR,LEDG,KEY,HEX7, HEX6, HEX5, HEX4, HEX3, HEX2, HEX1, HEX0);
	input [17:0] SW;
    input [3:0] KEY;
    output [0:6] HEX7, HEX6, HEX5, HEX4, HEX3, HEX2, HEX1, HEX0;
	output [17:0] LEDR;
	output [7:0] LEDG;
	
	wire [31:0] W_ALU_in_B,W_ALU_in_A,W_ALU_out,W_B_data,W_mux_2_out,W_Jump_addr,W_PC_in,W_PC_out,W_Mem_Read_data,W_instruction,W_MDR_out,W_ALU_out_hold,W_mux_1_out;
    wire [27:0] W_jump_28_bit;
	assign LEDR=W_PC_in[24:8];
	assign LEDG=W_PC_in[7:0];
	hex_ssd C0(W_ALU_out[3:0], HEX0);
	hex_ssd C1(W_ALU_out[7:4], HEX1);
	hex_ssd C2(W_Mem_Read_data[3:0],   HEX2);
	hex_ssd C3(W_Mem_Read_data[7:4],   HEX3);
	hex_ssd C4(W_mux_1_out[3:0],   HEX4);
	hex_ssd C5(W_mux_1_out[7:4],   HEX5);
	hex_ssd C6(W_MDR_out[3:0],HEX6);
	hex_ssd C7(W_MDR_out[7:4],HEX7);
	Datapath_Multi_cycle_Processor DUT(.clk(KEY[2]), .reset(SW[17]), .PCWr(SW[16]), .Iord(SW[15]), .MemWrite(SW[14]), .MemRead(SW[13]), .IRwrite(SW[12]), .MemtoReg(SW[11]), .RegWrite(SW[10]), .RegDst(SW[9]), .ALUSrcA(SW[8]), .ALUSrcB(SW[7:6]), .Operation_ALU(SW[5:3]), .PCSource(SW[2:1]), .ALU_in_B(W_ALU_in_B), .ALU_in_A(W_ALU_in_A), .ALU_out(W_ALU_out), .B_data(W_B_data), .mux_2_out(W_mux_2_out), .Jump_addr(W_Jump_addr), .PC_in(W_PC_in), .PC_out(W_PC_out), .Mem_Read_data(W_Mem_Read_data), .instruction(W_instruction), .MDR_out(W_MDR_out), .ALU_out_hold(W_ALU_out_hold), .jump_28_bit(W_jump_28_bit), .mux_1_out(W_mux_1_out));
endmodule


module  Datapath_Multi_cycle_Processor(clk, reset,Iord,MemWrite,MemtoReg,RegWrite,RegDst,ALUSrcA,PCWr,IRwrite,MemRead,ALUSrcB,PCSource,Operation_ALU,ALU_in_B,ALU_in_A,ALU_out,B_data,mux_2_out,Jump_addr,PC_in,PC_out,Mem_Read_data,instruction,MDR_out,ALU_out_hold,jump_28_bit,mux_1_out);
    input clk, reset;
    input Iord,MemWrite,MemtoReg,RegWrite,RegDst,ALUSrcA,PCWr,IRwrite,MemRead;
    input [1:0] ALUSrcB,PCSource;
    input [2:0] Operation_ALU;
    
    output [31:0] ALU_in_B,ALU_in_A,ALU_out,B_data,mux_2_out,Jump_addr,mux_1_out;
    output [31:0] PC_in,PC_out,Mem_Read_data,instruction,MDR_out,ALU_out_hold;
    
    output [27:0] jump_28_bit;
   
    wire [31:0] W_RD2, W_RD1,Extend_out,Branch_addr,A_data;
    wire [4:0] mux_3_out;
    wire zero,PCWrcond,and_out;

    Program_Counter     comp1(clk, reset, PCWr, PC_in, PC_out);
    Mux_32_bit          comp2(PC_out, ALU_out_hold, mux_1_out, Iord);
    Data_Memory         comp3(clk,mux_1_out, B_data, Mem_Read_data, MemRead, MemWrite);
    holding_reg         comp4(instruction, Mem_Read_data, IRwrite, clk, reset);
    holding_reg         comp5(MDR_out, Mem_Read_data, 1'b1, clk, reset);
    Mux_32_bit          comp6(MDR_out,ALU_out_hold, mux_2_out, MemtoReg);

    Register_File       comp7(clk,instruction[25:21], instruction[20:16], mux_3_out, W_RD1, W_RD2, mux_2_out, RegWrite);
    Mux_5_bit           comp8(instruction[20:16], instruction[15:11], mux_3_out, RegDst);
    Sign_Extension      comp9(instruction[15:0], Extend_out);
    shift_left_2        comp10(Extend_out, Branch_addr);
    holding_reg         comp11(A_data, W_RD1, 1'b1, clk, reset);
    holding_reg         comp12(B_data, W_RD2, 1'b1, clk, reset);
    Mux_32_bit          comp13(PC_out, A_data, ALU_in_A, ALUSrcA);
    Mux4_32_bit         comp14(B_data, 32'd4,Extend_out,Branch_addr , ALU_in_B, ALUSrcB);
    alu                 comp15(Operation_ALU, ALU_in_A, ALU_in_B, ALU_out,zero);
    holding_reg         comp16(ALU_out_hold, ALU_out , 1'b1, clk, reset);
    
    shift_left_2_28bit  comp17(instruction[25:0], jump_28_bit);
    
    concate             comp18(PC_out[31:28],jump_28_bit,Jump_addr);
    Mux4_32_bit         comp19(ALU_out, ALU_out_hold,Jump_addr, 32'b0, PC_in, PCSource);
    
endmodule

module Mux_5_bit (in0, in1, mux_out, select);
	parameter N = 5;
	input [N-1:0] in0, in1;
	output [N-1:0] mux_out;
	input select;
	assign mux_out = select? in1: in0 ;
endmodule

module Sign_Extension (sign_in, sign_out);
	input [15:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[15:0]=sign_in[15:0];
	assign sign_out[31:16]=sign_in[15]?16'b1111111111111111:16'b0;
endmodule

module Program_Counter (clk, reset, PC_write ,PC_in, PC_out);
	input clk, reset,PC_write;
	input [31:0] PC_in;
	output reg [31:0] PC_out;
	always @ (posedge clk or posedge reset)
	begin
		if(reset)
			PC_out <= 32'b0;
		else if (PC_write)
			PC_out <= PC_in;
	end
endmodule

module alu(
	input [2:0] alufn,
	input [31:0] ra,
	input [31:0] rb_or_imm,
	output reg [31:0] aluout,
	output reg zero);
	parameter	ALU_OP_ADD	    = 3'b000,
			    ALU_OP_SUB	    = 3'b001,
			    ALU_OP_AND	    = 3'b010,
			    ALU_OP_OR	    = 3'b011,
			    ALU_OP_XOR	    = 3'b100,
			    ALU_OP_LW	    = 3'b101,
			    ALU_OP_SW	    = 3'b110,
			    ALU_OP_BEQ	    = 3'b111;

    always @(*) 
        begin
		  case(alufn)
			ALU_OP_ADD 	    : aluout = ra + rb_or_imm;
			ALU_OP_SUB 	    : aluout = ra - rb_or_imm;
			ALU_OP_AND 	    : aluout = ra & rb_or_imm;
			ALU_OP_OR	    : aluout = ra | rb_or_imm;
			ALU_OP_XOR	    : aluout = ra ^ rb_or_imm;
			ALU_OP_LW	    : aluout = ra + rb_or_imm;
			ALU_OP_SW	    : aluout = ra + rb_or_imm;
			ALU_OP_BEQ	    : begin
					            zero = (ra==rb_or_imm)?1'b1:1'b0;
					            aluout = ra - rb_or_imm;
					          end
		  endcase
        end
endmodule

module Register_File (clk,read_addr_1, read_addr_2, write_addr, read_data_1, read_data_2, write_data, RegWrite);
	input [4:0] read_addr_1, read_addr_2, write_addr;
	input [31:0] write_data;
	input  clk,RegWrite;
	reg checkRegWrite;
	output reg [31:0] read_data_1, read_data_2;
	reg [31:0] Regfile [31:0];
	integer k;
	initial 
	    begin
	        for (k=0; k<32; k=k+1) 
			    begin
				    Regfile[k] = 32'd0;
			    end
			Regfile[8]=32'd1;//$t0
			Regfile[9]=32'd2;//$t1
			Regfile[10]=32'd3; //$t2
			Regfile[11]=32'd4; //$t3
			
			
			Regfile[17]=32'h99;//$s1
			Regfile[18]=32'h60;//$s2
			Regfile[19]=32'h30;//$s3
	    end
	
	//assign read_data_1 = Regfile[read_addr_1];
        always @(read_data_1 or Regfile[read_addr_1])
	        begin
	          if (read_addr_1 == 0) read_data_1 = 0;
	          else 
	          begin
	          read_data_1 = Regfile[read_addr_1];
	          //$display("read_addr_1=%d,read_data_1=%h",read_addr_1,read_data_1);
	          end
	        end
	//assign read_data_2 = Regfile[read_addr_2];
        always @(read_data_2 or Regfile[read_addr_2])
	        begin
	          if (read_addr_2 == 0) read_data_2 = 0;
	          else 
	          begin
	          read_data_2 = Regfile[read_addr_2];
	          //$display("read_addr_2=%d,read_data_2=%h",read_addr_2,read_data_2);
	          end
	        end
	always @(posedge clk)
	        begin
		      if (RegWrite == 1'b1)
		         begin 
		             Regfile[write_addr] = write_data;
		             $display("Register File write_addr=%d write_data=%d",write_addr,write_data);
		         end
	        end
endmodule

module holding_reg(output_data, input_data, write, clk, reset);
  // inputs
  input [31:0] input_data;
  input	write, clk, reset;

  // outputs
  output reg [31:0] output_data;

  // Register content and output assignment
    // update regisiter contents
  always @(posedge clk or posedge reset) 
  begin
    if (reset) 
    begin
      output_data <= 32'b0;
    end
    else if (write) 
    begin
      output_data <= input_data;
    end
  end
endmodule

module Mux_32_bit (in0, in1, mux_out, select);
	input [31:0] in0, in1;
	output [31:0] mux_out;
	input select;
	assign mux_out = select? in1: in0 ;
endmodule

module shift_left_2 (sign_in, sign_out);
	input [31:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[31:2]=sign_in[29:0];
	assign sign_out[1:0]=2'b00;
endmodule

module concate(PC_in,IR_in,PC_out);
    input [3:0] PC_in;
    input [27:0] IR_in;
    output[31:0] PC_out;
    assign PC_out={PC_in, IR_in};
endmodule

module Mux4_32_bit (in0, in1,in2, in3, mux_out, select);
	input [31:0] in0, in1,in2,in3;
	output [31:0] mux_out;
	input [1:0]select;
	assign mux_out = select[1]? (select[0]?in3: in2):(select[0]?in1:in0);
endmodule

module shift_left_2_28bit (sign_in, sign_out);
	input [25:0] sign_in;
	output [27:0] sign_out;
	assign sign_out={2'b00,sign_in};
endmodule

module Data_Memory (clk,addr, write_data, read_data, MemRead, MemWrite);
    input [31:0] addr;
    input [31:0] write_data;
    output [31:0] read_data;
    input MemRead, MemWrite,clk;
    reg [31:0] DMemory [63:0];
    integer k;
    initial begin
        for (k=0; k<64; k=k+1)
            begin
                DMemory[k] = 32'b0;
            end
        //sw  $s1, 0x02($s2)	    //	Memory[$s2+0x02] = $s1
        DMemory[0] = 32'b101011100101000100000000_0000_0010;       
        
        //add $s4,  $s2, $s3	    //	$s4 = $s2 + $s3  => R20=0x90 
        DMemory[4] = 32'b000000100101001110100000_0010_0000;
        
        
        //add $s5 $t0 $t1	    //r[21]=t0+t1=1+2=3 
        DMemory[8] = 32'b000000010000100110101000_0010_0000;
        
        
        //sub $s1, $s2, $s3	    //	$s1 = $s2   $s3  => R17=0x22=d30
        DMemory[12] = 32'b00000010010100111000100000100010;
        
        //sw  $s1, 0x02($s2)	    //	Memory[$s2+0x02] = $s1 = d30  //memory[62]=d30
        DMemory[16] = 32'b10101110010100010000000000000010;
        
        
        //lw $s1, 0x02($s2)	        //	$s1 = Memory[$s2+0x02]
        //R[17]=memory[62]=d30
        DMemory[20] = 32'b10001110010100010000000000000010;
        
        
        //beq $t2,$t3, End      //beq $t2,$t3, 0x03
        DMemory[24] = 32'b00010001010010110000000000000011;
        
        //addi $s7, $zero, 0x16  //R[23]=0x16
        DMemory[28] = 32'b00100000000101110000000000010000;
                
        //addi $s2, $zero, 0x55 //  load immediate value 0x55 to register $s2
        DMemory[32] = 32'b00100000000100100000000001010101;
        // //  load immediate value 0x22 to register $s3
        DMemory[36] = 32'b00100000000100110000000000100010;
        // //  load immediate value 0x77 to register $s5
        DMemory[40] = 32'b00100000000101010000000001110111;
        //j 0x00
        DMemory[44] = 32'b00001000000000000000000000000000;
        end
        
    assign read_data = (MemRead) ? DMemory[addr] : 32'bx;
    
    always @(posedge clk)
        begin
            if (MemWrite)
            begin
               DMemory[addr] = write_data;
               $display("Data memory write_addr=%d write_data=%d",addr,write_data);
            end
        end
endmodule

module hex_ssd (BIN, SSD);
  input [3:0] BIN;
  output reg [0:6] SSD;

  always@(*) begin
    case(BIN)
      0:SSD=7'b0000001;
      1:SSD=7'b1001111;
      2:SSD=7'b0010010;
      3:SSD=7'b0000110;
      4:SSD=7'b1001100;
      5:SSD=7'b0100100;
      6:SSD=7'b0100000;
      7:SSD=7'b0001111;
      8:SSD=7'b0000000;
      9:SSD=7'b0001100;
      10:SSD=7'b0001000;
      11:SSD=7'b1100000;
      12:SSD=7'b0110001;
      13:SSD=7'b1000010;
      14:SSD=7'b0110000;
      15:SSD=7'b0111000;
    endcase
  end
endmodule
