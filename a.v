module a (reset, clk, i1, z1, z2, z3);
input reset, clk, i1;
output z1, z2, z3;

reg [3:0] x;
//reg [3:0]y;

//assign z1 = (x == 256'd1125899906842625);
assign z1 = x[3] & x[0];
// & x[0];
//assign z1 = x > w;
assign z2 = (x <= 4'd9) && (x >= 4'd9);
assign z3 = (x > 4'd2);
//assign z4 = (x == 3'd2) || (y == 3'd5);

always @(posedge clk) begin
   if (!reset) begin
      x <= 4'd0;
   end
   else begin
      if ( x == 4'd0 ) begin
         x <= 4'd8;
      end
      else if (x == 4'd8) begin
        x <= 4'd10;
      end
      else if (x == 4'd10) begin
        x <= 4'd1;
      end
      else if (x == 4'd1) begin
        x <= 4'd2;
      end
      else if ((x == 4'd2) && (i1)) begin
        x <= 4'd5;
      end
      else if ((x == 4'd2) && (!i1)) begin
        x <= 4'd6;
      end
      else if (x == 4'd6) begin
        x <= 4'd7;
      end
      else if (x == 4'd7) begin
        x <= 4'd5;
      end
      else if ((x == 4'd5) && (!i1)) begin
        x <= 4'd1;
      end
      else if (x == 4'd5 && i1) begin
        x <= 4'd9;
      end
      else if (x == 4'd15) begin
        x <= 4'd9;
      end
      else if (x == 4'd14) begin
        x <= 4'd9;
      end
   end
end
endmodule

