module top( x0 , x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 , x9 , x10 , x11 , x12 , x13 , x14 , x15 , x16 , x17 , x18 , x19 , x20 , x21 , x22 , x23 , x24 , x25 , x26 , x27 , x28 , x29 , x30 , x31 , x32 , x33 , x34 , x35 , y0 , y1 , y2 , y3 , y4 , y5 , y6 );
  input x0 , x1 , x2 , x3 , x4 , x5 , x6 , x7 , x8 , x9 , x10 , x11 , x12 , x13 , x14 , x15 , x16 , x17 , x18 , x19 , x20 , x21 , x22 , x23 , x24 , x25 , x26 , x27 , x28 , x29 , x30 , x31 , x32 , x33 , x34 , x35 ;
  output y0 , y1 , y2 , y3 , y4 , y5 , y6 ;
  wire n37 , n38 , n39 , n40 , n41 , n42 , n43 , n44 , n45 , n46 , n47 , n48 , n49 , n50 , n51 , n52 , n53 , n54 , n55 , n56 , n57 , n58 , n59 , n60 , n61 , n62 , n63 , n64 , n65 , n66 , n67 , n68 , n69 , n70 , n71 , n72 , n73 , n74 , n75 , n76 , n77 , n78 , n79 , n80 , n81 , n82 , n83 , n84 , n85 , n86 , n87 , n88 , n89 , n90 , n91 , n92 , n93 , n94 , n95 , n96 , n97 , n98 , n99 , n100 , n101 , n102 , n103 , n104 , n105 , n106 , n107 , n108 , n109 , n110 , n111 , n112 , n113 , n114 , n115 , n116 , n117 , n118 , n119 , n120 , n121 , n122 , n123 , n124 , n125 , n126 , n127 , n128 , n129 , n130 , n131 , n132 , n133 , n134 , n135 , n136 , n137 , n138 , n139 , n140 , n141 , n142 , n143 , n144 , n145 , n146 , n147 , n148 , n149 , n150 , n151 , n152 , n153 , n154 , n155 , n156 , n157 , n158 , n159 , n160 , n161 , n162 , n163 , n164 , n165 , n166 , n167 , n168 , n169 , n170 , n171 , n172 , n173 , n174 , n175 , n176 , n177 , n178 , n179 , n180 , n181 , n182 , n183 , n184 , n185 , n186 , n187 , n188 , n189 , n190 , n191 , n192 , n193 , n194 , n195 , n196 , n197 , n198 , n199 , n200 , n201 , n202 , n203 , n204 , n205 , n206 , n207 , n208 , n209 , n210 ;
  assign n37 = x19 | x21 ;
  assign n38 = ~x15 & x17 ;
  assign n39 = x7 | x9 ;
  assign n40 = ~x0 & x1 ;
  assign n41 = ~x3 & x5 ;
  assign n42 = n40 | n41 ;
  assign n43 = ( ~x7 & n39 ) | ( ~x7 & n42 ) | ( n39 & n42 ) ;
  assign n44 = x13 | n43 ;
  assign n45 = ( ~x11 & n43 ) | ( ~x11 & n44 ) | ( n43 & n44 ) ;
  assign n46 = n38 | n45 ;
  assign n47 = ( ~x19 & n37 ) | ( ~x19 & n46 ) | ( n37 & n46 ) ;
  assign n48 = x25 | n47 ;
  assign n49 = ( ~x23 & n47 ) | ( ~x23 & n48 ) | ( n47 & n48 ) ;
  assign n50 = x29 | n49 ;
  assign n51 = ( ~x27 & n49 ) | ( ~x27 & n50 ) | ( n49 & n50 ) ;
  assign n52 = x31 & ~n51 ;
  assign n53 = ( x33 & n51 ) | ( x33 & ~n52 ) | ( n51 & ~n52 ) ;
  assign n54 = ~x31 & n51 ;
  assign n55 = x33 & ~x34 ;
  assign n56 = ( ~n51 & n54 ) | ( ~n51 & n55 ) | ( n54 & n55 ) ;
  assign n57 = ( x27 & ~x29 ) | ( x27 & n53 ) | ( ~x29 & n53 ) ;
  assign n58 = ( x27 & ~x30 ) | ( x27 & n53 ) | ( ~x30 & n53 ) ;
  assign n59 = ~n57 & n58 ;
  assign n60 = ( x23 & ~x25 ) | ( x23 & n53 ) | ( ~x25 & n53 ) ;
  assign n61 = ( x23 & ~x26 ) | ( x23 & n53 ) | ( ~x26 & n53 ) ;
  assign n62 = ~n60 & n61 ;
  assign n63 = ( x15 & ~x17 ) | ( x15 & n53 ) | ( ~x17 & n53 ) ;
  assign n64 = ( x15 & ~x18 ) | ( x15 & n53 ) | ( ~x18 & n53 ) ;
  assign n65 = ~n63 & n64 ;
  assign n66 = ( x19 & ~x21 ) | ( x19 & n53 ) | ( ~x21 & n53 ) ;
  assign n67 = ( x19 & ~x22 ) | ( x19 & n53 ) | ( ~x22 & n53 ) ;
  assign n68 = ~n66 & n67 ;
  assign n69 = ( x11 & ~x13 ) | ( x11 & n53 ) | ( ~x13 & n53 ) ;
  assign n70 = ( x11 & ~x14 ) | ( x11 & n53 ) | ( ~x14 & n53 ) ;
  assign n71 = ~n69 & n70 ;
  assign n72 = ( x0 & ~x1 ) | ( x0 & n53 ) | ( ~x1 & n53 ) ;
  assign n73 = ( x0 & ~x2 ) | ( x0 & n53 ) | ( ~x2 & n53 ) ;
  assign n74 = ~n72 & n73 ;
  assign n75 = ( x7 & ~x9 ) | ( x7 & n53 ) | ( ~x9 & n53 ) ;
  assign n76 = ( x7 & ~x10 ) | ( x7 & n53 ) | ( ~x10 & n53 ) ;
  assign n77 = ~n75 & n76 ;
  assign n78 = ( x3 & ~x5 ) | ( x3 & n53 ) | ( ~x5 & n53 ) ;
  assign n79 = ( x3 & ~x6 ) | ( x3 & n53 ) | ( ~x6 & n53 ) ;
  assign n80 = ~n78 & n79 ;
  assign n81 = n77 | n80 ;
  assign n82 = ( ~n71 & n74 ) | ( ~n71 & n81 ) | ( n74 & n81 ) ;
  assign n83 = n71 | n82 ;
  assign n84 = n68 | n83 ;
  assign n85 = ( ~n62 & n65 ) | ( ~n62 & n84 ) | ( n65 & n84 ) ;
  assign n86 = n62 | n85 ;
  assign n87 = n59 | n86 ;
  assign n88 = n56 | n87 ;
  assign n89 = ( x3 & ~x8 ) | ( x3 & n53 ) | ( ~x8 & n53 ) ;
  assign n90 = ~n78 & n89 ;
  assign n91 = ( n80 & ~n88 ) | ( n80 & n90 ) | ( ~n88 & n90 ) ;
  assign n92 = ~n80 & n91 ;
  assign n93 = ( n88 & n91 ) | ( n88 & n92 ) | ( n91 & n92 ) ;
  assign n94 = ~n74 & n88 ;
  assign n95 = ( x0 & ~x4 ) | ( x0 & n53 ) | ( ~x4 & n53 ) ;
  assign n96 = ~n72 & n95 ;
  assign n97 = ( ~n74 & n88 ) | ( ~n74 & n96 ) | ( n88 & n96 ) ;
  assign n98 = ( n93 & ~n94 ) | ( n93 & n97 ) | ( ~n94 & n97 ) ;
  assign n99 = n77 & ~n88 ;
  assign n100 = ( x7 & ~x12 ) | ( x7 & n53 ) | ( ~x12 & n53 ) ;
  assign n101 = ~n75 & n100 ;
  assign n102 = ( n77 & ~n88 ) | ( n77 & n101 ) | ( ~n88 & n101 ) ;
  assign n103 = ( n98 & ~n99 ) | ( n98 & n102 ) | ( ~n99 & n102 ) ;
  assign n104 = n71 & ~n88 ;
  assign n105 = ( x11 & ~x16 ) | ( x11 & n53 ) | ( ~x16 & n53 ) ;
  assign n106 = ~n69 & n105 ;
  assign n107 = ( n71 & ~n88 ) | ( n71 & n106 ) | ( ~n88 & n106 ) ;
  assign n108 = ( n103 & ~n104 ) | ( n103 & n107 ) | ( ~n104 & n107 ) ;
  assign n109 = n65 & ~n88 ;
  assign n110 = ( x15 & ~x20 ) | ( x15 & n53 ) | ( ~x20 & n53 ) ;
  assign n111 = ~n63 & n110 ;
  assign n112 = ( n65 & ~n88 ) | ( n65 & n111 ) | ( ~n88 & n111 ) ;
  assign n113 = ( n108 & ~n109 ) | ( n108 & n112 ) | ( ~n109 & n112 ) ;
  assign n114 = n68 & ~n88 ;
  assign n115 = ( x19 & ~x24 ) | ( x19 & n53 ) | ( ~x24 & n53 ) ;
  assign n116 = ~n66 & n115 ;
  assign n117 = ( n68 & ~n88 ) | ( n68 & n116 ) | ( ~n88 & n116 ) ;
  assign n118 = ( n113 & ~n114 ) | ( n113 & n117 ) | ( ~n114 & n117 ) ;
  assign n119 = n62 & ~n88 ;
  assign n120 = ( x23 & ~x28 ) | ( x23 & n53 ) | ( ~x28 & n53 ) ;
  assign n121 = ~n60 & n120 ;
  assign n122 = ( n62 & ~n88 ) | ( n62 & n121 ) | ( ~n88 & n121 ) ;
  assign n123 = ( n118 & ~n119 ) | ( n118 & n122 ) | ( ~n119 & n122 ) ;
  assign n124 = n59 & ~n88 ;
  assign n125 = ( x27 & ~x32 ) | ( x27 & n53 ) | ( ~x32 & n53 ) ;
  assign n126 = ~n57 & n125 ;
  assign n127 = ( n59 & ~n88 ) | ( n59 & n126 ) | ( ~n88 & n126 ) ;
  assign n128 = ( n123 & ~n124 ) | ( n123 & n127 ) | ( ~n124 & n127 ) ;
  assign n129 = ~n56 & n88 ;
  assign n130 = x33 & ~x35 ;
  assign n131 = ( ~n51 & n54 ) | ( ~n51 & n130 ) | ( n54 & n130 ) ;
  assign n132 = ( ~n56 & n88 ) | ( ~n56 & n131 ) | ( n88 & n131 ) ;
  assign n133 = ( n128 & ~n129 ) | ( n128 & n132 ) | ( ~n129 & n132 ) ;
  assign n134 = ~x35 & n133 ;
  assign n135 = x34 & n88 ;
  assign n136 = n53 | n135 ;
  assign n137 = ( x31 & n135 ) | ( x31 & n136 ) | ( n135 & n136 ) ;
  assign n138 = x33 & ~n137 ;
  assign n139 = ( ~n133 & n134 ) | ( ~n133 & n138 ) | ( n134 & n138 ) ;
  assign n140 = ~x28 & n133 ;
  assign n141 = x26 & n88 ;
  assign n142 = n53 | n141 ;
  assign n143 = ( x23 & n141 ) | ( x23 & n142 ) | ( n141 & n142 ) ;
  assign n144 = x25 & ~n143 ;
  assign n145 = ( ~n133 & n140 ) | ( ~n133 & n144 ) | ( n140 & n144 ) ;
  assign n146 = ~x32 & n133 ;
  assign n147 = x30 & n88 ;
  assign n148 = n53 | n147 ;
  assign n149 = ( x27 & n147 ) | ( x27 & n148 ) | ( n147 & n148 ) ;
  assign n150 = x29 & ~n149 ;
  assign n151 = ( ~n133 & n146 ) | ( ~n133 & n150 ) | ( n146 & n150 ) ;
  assign n152 = ~x24 & n133 ;
  assign n153 = x22 & n88 ;
  assign n154 = n53 | n153 ;
  assign n155 = ( x19 & n153 ) | ( x19 & n154 ) | ( n153 & n154 ) ;
  assign n156 = x21 & ~n155 ;
  assign n157 = ( ~n133 & n152 ) | ( ~n133 & n156 ) | ( n152 & n156 ) ;
  assign n158 = ~x16 & n133 ;
  assign n159 = x14 & n88 ;
  assign n160 = n53 | n159 ;
  assign n161 = ( x11 & n159 ) | ( x11 & n160 ) | ( n159 & n160 ) ;
  assign n162 = x13 & ~n161 ;
  assign n163 = ( ~n133 & n158 ) | ( ~n133 & n162 ) | ( n158 & n162 ) ;
  assign n164 = ~x20 & n133 ;
  assign n165 = x18 & n88 ;
  assign n166 = n53 | n165 ;
  assign n167 = ( x15 & n165 ) | ( x15 & n166 ) | ( n165 & n166 ) ;
  assign n168 = x17 & ~n167 ;
  assign n169 = ( ~n133 & n164 ) | ( ~n133 & n168 ) | ( n164 & n168 ) ;
  assign n170 = ~x8 & n133 ;
  assign n171 = x6 & n88 ;
  assign n172 = n53 | n171 ;
  assign n173 = ( x3 & n171 ) | ( x3 & n172 ) | ( n171 & n172 ) ;
  assign n174 = x5 & ~n173 ;
  assign n175 = ( ~n133 & n170 ) | ( ~n133 & n174 ) | ( n170 & n174 ) ;
  assign n176 = ~x12 & n133 ;
  assign n177 = x10 & n88 ;
  assign n178 = n53 | n177 ;
  assign n179 = ( x7 & n177 ) | ( x7 & n178 ) | ( n177 & n178 ) ;
  assign n180 = x9 & ~n179 ;
  assign n181 = ( ~n133 & n176 ) | ( ~n133 & n180 ) | ( n176 & n180 ) ;
  assign n182 = n175 | n181 ;
  assign n183 = n169 | n182 ;
  assign n184 = ( ~n157 & n163 ) | ( ~n157 & n183 ) | ( n163 & n183 ) ;
  assign n185 = n157 | n184 ;
  assign n186 = n151 | n185 ;
  assign n187 = ( ~n139 & n145 ) | ( ~n139 & n186 ) | ( n145 & n186 ) ;
  assign n188 = n139 | n187 ;
  assign n189 = ~x0 & n53 ;
  assign n190 = x4 & n133 ;
  assign n191 = n88 | n190 ;
  assign n192 = ( x2 & n190 ) | ( x2 & n191 ) | ( n190 & n191 ) ;
  assign n193 = x1 & ~n192 ;
  assign n194 = ( ~n53 & n189 ) | ( ~n53 & n193 ) | ( n189 & n193 ) ;
  assign n195 = n188 & ~n194 ;
  assign n196 = n163 & ~n181 ;
  assign n197 = n182 | n196 ;
  assign n198 = n169 | n197 ;
  assign n199 = n163 | n181 ;
  assign n200 = n169 | n199 ;
  assign n201 = n157 & ~n200 ;
  assign n202 = ( n163 & n169 ) | ( n163 & ~n201 ) | ( n169 & ~n201 ) ;
  assign n203 = n145 & n202 ;
  assign n204 = ( n145 & n201 ) | ( n145 & ~n203 ) | ( n201 & ~n203 ) ;
  assign n205 = n182 | n204 ;
  assign n206 = ( ~n145 & n151 ) | ( ~n145 & n201 ) | ( n151 & n201 ) ;
  assign n207 = n199 | n206 ;
  assign n208 = ( ~n199 & n201 ) | ( ~n199 & n207 ) | ( n201 & n207 ) ;
  assign n209 = n196 | n208 ;
  assign n210 = n175 | n209 ;
  assign y0 = n53 ;
  assign y1 = n88 ;
  assign y2 = n133 ;
  assign y3 = n195 ;
  assign y4 = n198 ;
  assign y5 = n205 ;
  assign y6 = n210 ;
endmodule