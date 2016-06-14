module a (reset, clk, i1, z1);
input reset, clk, i1;
output z1;

reg [2:0] x;
//reg [3:0]y;

//assign z1 = (x == 256'd1125899906842625);
assign z1 = x[2] & x[0];
//assign z1 = x > w;
//assign z2 = (x <= 3'd7) && (x >= 3'd7);
//assign z3 = (x > 3'd2);
//assign z4 = (x == 3'd2) || (y == 3'd5);

always @(posedge clk) begin
   if (!reset) begin
      x <= 3'd0;
   end
   else begin
      if ( x == 3'd0 ) begin
         x <= 3'd2;
      end
      else if (x == 3'd2) begin
        x <= 3'd6;
      end
      else if (x == 3'd6) begin
        x <= 3'd0;
      end
/*      else if (x == 3'd1) begin
        x <= 3'd4;
      end
      else if (x == 3'd4) begin
        x <= 3'd6;
      end
      else if (x == 3'd6) begin
        x <= 3'd1;
      end*/
//      else if (x == 3'd5) begin
//        x <= 3'd7;
//      end
      else if (x == 3'd3) begin
        x <= 3'd7;
      end
   end
end
endmodule

