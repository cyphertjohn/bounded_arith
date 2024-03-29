open Bound.Expr;;
open SymBoundBenchmark

let t1 = from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) - drop"
let t2 = from_string "(t1 - startTime) drop - diff1"
let t3 = from_string "startPrice - diff1 - price1"

let vars_to_keep = ["minimumPrice"; "startPrice"; "startTime"; "endTime"; "t1"]


let () = Bound.Log.log_times := true

let () = SymBoundBenchmark.process_cmdline ()
let sat_bound = SymBoundBenchmark.sat_bound ()
let use_proj = not (SymBoundBenchmark.use_lp ())

let tupperAndTlower = Bound.Log.log_time "Rewrite total" (Bound.Rewriter.rewrite ~use_proj:use_proj ~sat:sat_bound  [t1;t2;t3] 
									  [from_string "startPrice - minimumPrice";
									  	from_string "endTime - startTime";
									  	from_string "t1 - startTime";
									  	from_string "endTime - t1"]
									  vars_to_keep)
									  [(from_string "price1")]



let price1uppers, price1lowers = List.hd tupperAndTlower

let () = Bound.Log.log_line_s "price1 upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) price1uppers
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "price1 lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) price1lowers
let () = Bound.Log.log_line_s ""