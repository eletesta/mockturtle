module top( x0 , x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 , x9 , x10 , x11 , x12 , x13 , x14 , x15 , x16 , x17 , x18 , x19 , x20 , x21 , x22 , x23 , x24 , x25 , x26 , y0 , y1 , y2 , y3 , y4 , y5 , y6 );
  input x0 , x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 , x9 , x10 , x11 , x12 , x13 , x14 , x15 , x16 , x17 , x18 , x19 , x20 , x21 , x22 , x23 , x24 , x25 , x26 ;
  output y0 , y1 , y2 , y3 , y4 , y5 , y6 ;
  wire n28 , n29 , n30 , n31 , n32 , n33 , n34 , n35 , n36 , n37 , n38 , n39 , n40 , n41 , n42 , n43 , n44 , n45 , n46 , n47 , n48 , n49 , n50 , n51 , n52 , n53 , n54 , n55 , n56 , n57 , n58 , n59 , n60 , n61 , n62 , n63 , n64 , n65 , n66 , n67 , n68 , n69 , n70 , n71 , n72 , n73 , n74 , n75 , n76 , n77 , n78 , n79 , n80 , n81 , n82 , n83 , n84 , n85 , n86 , n87 , n88 , n89 , n90 , n91 , n92 , n93 , n94 , n95 , n96 , n97 , n98 , n99 , n100 , n101 , n102 , n103 , n104 , n105 , n106 , n107 , n108 , n109 , n110 , n111 , n112 , n113 , n114 , n115 , n116 , n117 , n118 , n119 , n120 , n121 , n122 , n123 , n124 , n125 , n126 , n127 , n128 , n129 , n130 , n131 , n132 , n133 , n134 , n135 , n136 , n137 , n138 , n139 , n140 , n141 , n142 , n143 , n144 , n145 , n146 , n147 , n148 , n149 , n150 , n151 , n152 , n153 , n154 , n155 , n156 , n157 , n158 , n159 , n160 , n161 , n162 , n163 , n164 , n165 , n166 , n167 , n168 , n169 , n170 , n171 , n172 , n173 , n174 , n175 , n176 , n177 , n178 , n179 , n180 , n181 ;
  assign n28 = x8 & ~x9 ;
  assign n29 = ~x7 & x8 ;
  assign n30 = x9 & n29 ;
  assign n31 = ( x9 & n28 ) | ( x9 & ~n30 ) | ( n28 & ~n30 ) ;
  assign n32 = x6 | n31 ;
  assign n33 = x10 & ~x11 ;
  assign n34 = ( x7 & ~x12 ) | ( x7 & n33 ) | ( ~x12 & n33 ) ;
  assign n35 = ~x7 & n34 ;
  assign n36 = ~x8 & x9 ;
  assign n37 = x7 & x13 ;
  assign n38 = ( x8 & n36 ) | ( x8 & n37 ) | ( n36 & n37 ) ;
  assign n39 = n35 | n38 ;
  assign n40 = ( ~n31 & n32 ) | ( ~n31 & n39 ) | ( n32 & n39 ) ;
  assign n41 = x3 & x5 ;
  assign n42 = ( x4 & ~n40 ) | ( x4 & n41 ) | ( ~n40 & n41 ) ;
  assign n43 = n40 & n42 ;
  assign n44 = x0 & x2 ;
  assign n45 = ( x1 & ~n43 ) | ( x1 & n44 ) | ( ~n43 & n44 ) ;
  assign n46 = n43 & n45 ;
  assign n47 = ~x11 & x15 ;
  assign n48 = ~x12 & n47 ;
  assign n49 = ( x8 & x9 ) | ( x8 & n48 ) | ( x9 & n48 ) ;
  assign n50 = x14 & ~n49 ;
  assign n51 = ( x14 & n48 ) | ( x14 & ~n50 ) | ( n48 & ~n50 ) ;
  assign n52 = ~x8 & x14 ;
  assign n53 = ~x9 & n52 ;
  assign n54 = ( ~x7 & n51 ) | ( ~x7 & n53 ) | ( n51 & n53 ) ;
  assign n55 = x9 & x16 ;
  assign n56 = ( x8 & x16 ) | ( x8 & n55 ) | ( x16 & n55 ) ;
  assign n57 = ( x7 & n53 ) | ( x7 & n56 ) | ( n53 & n56 ) ;
  assign n58 = n54 | n57 ;
  assign n59 = x3 | x5 ;
  assign n60 = ( x4 & n58 ) | ( x4 & n59 ) | ( n58 & n59 ) ;
  assign n61 = n58 & ~n60 ;
  assign n62 = ~x1 & n61 ;
  assign n63 = ( x0 & ~x2 ) | ( x0 & n62 ) | ( ~x2 & n62 ) ;
  assign n64 = ~x0 & n63 ;
  assign n65 = ( x21 & x22 ) | ( x21 & x23 ) | ( x22 & x23 ) ;
  assign n66 = ~x20 & x21 ;
  assign n67 = ( ~x22 & n65 ) | ( ~x22 & n66 ) | ( n65 & n66 ) ;
  assign n68 = ( x17 & x18 ) | ( x17 & n67 ) | ( x18 & n67 ) ;
  assign n69 = x17 & ~x19 ;
  assign n70 = ( ~n67 & n68 ) | ( ~n67 & n69 ) | ( n68 & n69 ) ;
  assign n71 = ( ~x21 & x22 ) | ( ~x21 & x23 ) | ( x22 & x23 ) ;
  assign n72 = x20 & ~x21 ;
  assign n73 = ( ~x23 & n71 ) | ( ~x23 & n72 ) | ( n71 & n72 ) ;
  assign n74 = ( x17 & ~x18 ) | ( x17 & n73 ) | ( ~x18 & n73 ) ;
  assign n75 = ~x17 & x19 ;
  assign n76 = ( x18 & n74 ) | ( x18 & ~n75 ) | ( n74 & ~n75 ) ;
  assign n77 = n58 & n76 ;
  assign n78 = n40 | n77 ;
  assign n79 = ( ~n70 & n77 ) | ( ~n70 & n78 ) | ( n77 & n78 ) ;
  assign n80 = ( x1 & x2 ) | ( x1 & ~x4 ) | ( x2 & ~x4 ) ;
  assign n81 = x3 & ~x4 ;
  assign n82 = ( ~x2 & n80 ) | ( ~x2 & n81 ) | ( n80 & n81 ) ;
  assign n83 = ( x1 & x2 ) | ( x1 & x4 ) | ( x2 & x4 ) ;
  assign n84 = ~x3 & x4 ;
  assign n85 = ( ~x1 & n83 ) | ( ~x1 & n84 ) | ( n83 & n84 ) ;
  assign n86 = ~x5 & n40 ;
  assign n87 = ( n40 & n85 ) | ( n40 & n86 ) | ( n85 & n86 ) ;
  assign n88 = ( x5 & ~n82 ) | ( x5 & n87 ) | ( ~n82 & n87 ) ;
  assign n89 = n58 | n87 ;
  assign n90 = ( n82 & n88 ) | ( n82 & n89 ) | ( n88 & n89 ) ;
  assign n91 = x0 | x2 ;
  assign n92 = x1 | n91 ;
  assign n93 = x3 | x4 ;
  assign n94 = x14 & ~n93 ;
  assign n95 = ( x5 & ~n92 ) | ( x5 & n94 ) | ( ~n92 & n94 ) ;
  assign n96 = ~x5 & n95 ;
  assign n97 = x1 & n44 ;
  assign n98 = x3 & x4 ;
  assign n99 = x6 & n98 ;
  assign n100 = ( x5 & ~n97 ) | ( x5 & n99 ) | ( ~n97 & n99 ) ;
  assign n101 = n97 & n100 ;
  assign n102 = x18 & x20 ;
  assign n103 = ( ~x17 & x19 ) | ( ~x17 & n102 ) | ( x19 & n102 ) ;
  assign n104 = x17 & n103 ;
  assign n105 = x22 & x26 ;
  assign n106 = ( ~x21 & x23 ) | ( ~x21 & n105 ) | ( x23 & n105 ) ;
  assign n107 = x21 & n106 ;
  assign n108 = n104 & n107 ;
  assign n109 = n101 & n108 ;
  assign n110 = x18 | x20 ;
  assign n111 = ( ~x17 & x19 ) | ( ~x17 & n110 ) | ( x19 & n110 ) ;
  assign n112 = x17 | n111 ;
  assign n113 = x22 | x26 ;
  assign n114 = ( ~x21 & x23 ) | ( ~x21 & n113 ) | ( x23 & n113 ) ;
  assign n115 = x21 | n114 ;
  assign n116 = n112 | n115 ;
  assign n117 = ~n109 & n116 ;
  assign n118 = ( n96 & n109 ) | ( n96 & ~n117 ) | ( n109 & ~n117 ) ;
  assign n119 = n31 & n118 ;
  assign n120 = x10 & n98 ;
  assign n121 = ( x5 & ~n97 ) | ( x5 & n120 ) | ( ~n97 & n120 ) ;
  assign n122 = n97 & n121 ;
  assign n123 = n108 & n122 ;
  assign n124 = x15 & ~n93 ;
  assign n125 = ( x5 & ~n92 ) | ( x5 & n124 ) | ( ~n92 & n124 ) ;
  assign n126 = ~x5 & n125 ;
  assign n127 = n123 | n126 ;
  assign n128 = ( ~n116 & n123 ) | ( ~n116 & n127 ) | ( n123 & n127 ) ;
  assign n129 = x7 | x12 ;
  assign n130 = ( x11 & n128 ) | ( x11 & n129 ) | ( n128 & n129 ) ;
  assign n131 = n128 & ~n130 ;
  assign n132 = x13 & n98 ;
  assign n133 = ( x5 & ~n97 ) | ( x5 & n132 ) | ( ~n97 & n132 ) ;
  assign n134 = n97 & n133 ;
  assign n135 = n108 & n134 ;
  assign n136 = x16 & ~n93 ;
  assign n137 = ( x5 & ~n92 ) | ( x5 & n136 ) | ( ~n92 & n136 ) ;
  assign n138 = ~x5 & n137 ;
  assign n139 = n135 | n138 ;
  assign n140 = ( ~n116 & n135 ) | ( ~n116 & n139 ) | ( n135 & n139 ) ;
  assign n141 = x7 & n140 ;
  assign n142 = ( x8 & n36 ) | ( x8 & n141 ) | ( n36 & n141 ) ;
  assign n143 = n131 | n142 ;
  assign n144 = ( n118 & ~n119 ) | ( n118 & n143 ) | ( ~n119 & n143 ) ;
  assign n145 = ~x25 & n144 ;
  assign n146 = ( ~x24 & n144 ) | ( ~x24 & n145 ) | ( n144 & n145 ) ;
  assign n147 = x1 & x3 ;
  assign n148 = ( ~x0 & x2 ) | ( ~x0 & n147 ) | ( x2 & n147 ) ;
  assign n149 = x0 & n148 ;
  assign n150 = x4 & x5 ;
  assign n151 = x17 & n150 ;
  assign n152 = ( x6 & ~n149 ) | ( x6 & n151 ) | ( ~n149 & n151 ) ;
  assign n153 = n149 & n152 ;
  assign n154 = x4 | x5 ;
  assign n155 = x1 | x3 ;
  assign n156 = ( ~x0 & x2 ) | ( ~x0 & n155 ) | ( x2 & n155 ) ;
  assign n157 = x0 | n156 ;
  assign n158 = n154 | n157 ;
  assign n159 = ( x14 & x17 ) | ( x14 & ~n158 ) | ( x17 & ~n158 ) ;
  assign n160 = ~x17 & n159 ;
  assign n161 = x17 | n154 ;
  assign n162 = x16 & ~n161 ;
  assign n163 = x13 & n151 ;
  assign n164 = n149 & n163 ;
  assign n165 = n157 & ~n164 ;
  assign n166 = ( n162 & n164 ) | ( n162 & ~n165 ) | ( n164 & ~n165 ) ;
  assign n167 = x9 & n166 ;
  assign n168 = ( x8 & n166 ) | ( x8 & n167 ) | ( n166 & n167 ) ;
  assign n169 = x7 & ~n168 ;
  assign n170 = x10 & n151 ;
  assign n171 = ( x12 & ~n149 ) | ( x12 & n170 ) | ( ~n149 & n170 ) ;
  assign n172 = ( x15 & x17 ) | ( x15 & ~n158 ) | ( x17 & ~n158 ) ;
  assign n173 = ~x17 & n172 ;
  assign n174 = ~x12 & n173 ;
  assign n175 = ( n170 & ~n171 ) | ( n170 & n174 ) | ( ~n171 & n174 ) ;
  assign n176 = ~x11 & n175 ;
  assign n177 = x7 | n176 ;
  assign n178 = ~n169 & n177 ;
  assign n179 = ( ~n153 & n160 ) | ( ~n153 & n178 ) | ( n160 & n178 ) ;
  assign n180 = n31 & ~n178 ;
  assign n181 = ( n153 & n179 ) | ( n153 & ~n180 ) | ( n179 & ~n180 ) ;
  assign y0 = n46 ;
  assign y1 = n64 ;
  assign y2 = n79 ;
  assign y3 = n90 ;
  assign y4 = n146 ;
  assign y5 = n144 ;
  assign y6 = n181 ;
endmodule