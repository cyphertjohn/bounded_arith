open Bound.Expr;;
open SymBoundBenchmark

let t1 = from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) - drop"
let t2 = from_string "(t1 - startTime) drop - diff1"
let t3 = from_string "startPrice - diff1 - price1"

let t1_2 = from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) - drop" 
let t2_2 = from_string "(t2 - startTime) drop - diff2" 
let t3_2 = from_string "startPrice - diff2 - price2" 

let vars_to_keep = ["minimumPrice"; "startPrice"; "startTime"; "endTime"; "t1"]


let () = Bound.Log.log_times := true

let () = SymBoundBenchmark.process_cmdline ()
let sat_bound = SymBoundBenchmark.sat_bound ()
let compute_hull = SymBoundBenchmark.compute_hull ()
let use_proj = not (SymBoundBenchmark.use_lp ())

let tupperAndTlower = Bound.Log.log_time "Rewrite total" (Bound.Rewriter.rewrite ~use_proj:use_proj ~sat:sat_bound ~compute_hull:compute_hull [t1;t2;t3;t1_2;t2_2;t3_2] 
									  [from_string "startPrice - minimumPrice";
									  	from_string "endTime - startTime";
									  	from_string "t1 - startTime";
										from_string "t2 - t1";
										from_string "endTime - t2"]
									  vars_to_keep)
									  [(from_string "price2 - price1")]



let price2diffprice1upper, price2diffprice1lower = List.hd tupperAndTlower

let () = Bound.Log.log_line_s "price2 - price1 upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) price2diffprice1upper
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "price2 - price1 lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) price2diffprice1lower
let () = Bound.Log.log_line_s ""