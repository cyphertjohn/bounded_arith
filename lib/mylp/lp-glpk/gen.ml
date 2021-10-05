let () = 
  let c_out = open_out "stub.c" in
  let ml_out = open_out "stub.ml" in
  Cstubs.write_ml (Format.formatter_of_out_channel ml_out) ~prefix:"lp_stub" (module Bindings.Bindings);
  output_string c_out "#include <glpk.h>\n";
  Cstubs.write_c (Format.formatter_of_out_channel c_out) ~prefix:"lp_stub" (module Bindings.Bindings);
  flush c_out;
  flush ml_out;
  close_out c_out;
  close_out ml_out

