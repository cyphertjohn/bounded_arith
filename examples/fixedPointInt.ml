open Bound.Expr
open SymBoundBenchmark

let vars_to_keep = ["a"; "b"; "sf"]

let () = Bound.Log.log_times := true

let () = SymBoundBenchmark.process_cmdline ()
let sat_bound = SymBoundBenchmark.sat_bound ()
let use_proj = not (SymBoundBenchmark.use_lp ())

let rewrites = Bound.Log.log_time "Rewrite mult/div total" (Bound.Rewriter.rewrite ~use_proj:use_proj ~sat:sat_bound [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  [from_string "floor((floor((a b) / (sf)) sf) / (b))"]


let tmuldivinv_upper, tmuldivinv_lower = List.nth rewrites 0

let () = Bound.Log.log_line_s "tmuldivinv upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tmuldivinv_upper
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "tmuldivinv lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tmuldivinv_lower
let () = Bound.Log.log_line_s ""