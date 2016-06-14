module a (reset, clk, i1, z1);
input reset, clk, i1;
output z1;

reg [1:0] x;
//reg [3:0]y;

//assign z1 = (x == 256'd1125899906842625);
assign z1 = x[1] & x[0];
//assign z1 = x > w;
//assign z2 = (x <= 3'd7) && (x >= 3'd7);
//assign z3 = (x > 3'd2);
//assign z4 = (x == 3'd2) || (y == 3'd5);

always @(posedge clk) begin
   if (!reset) begin
      x <= 2'd0;
   end
   else begin
      if ( x == 2'd0 ) begin
         x <= 2'd1;
      end
      else if (x == 2'd1) begin
        x <= 2'd2;
      end
      else if (x == 2'd2) begin
        x <= 2'd3;
      end
   end
end
endmodule

