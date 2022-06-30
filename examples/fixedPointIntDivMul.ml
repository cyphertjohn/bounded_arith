open Bound.Expr
open SymBoundBenchmark

let vars_to_keep = ["a"; "b"; "sf"]

let () = Bound.Log.log_times := true

let () = SymBoundBenchmark.process_cmdline ()
let sat_bound = SymBoundBenchmark.sat_bound ()
let compute_hull = SymBoundBenchmark.compute_hull ()
let use_proj = not (SymBoundBenchmark.use_lp ())

let rewrites = Bound.Log.log_time "Rewrite mult/div total" (Bound.Rewriter.rewrite ~use_proj:use_proj ~sat:sat_bound ~compute_hull:compute_hull [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  [from_string "floor((b floor((a sf) / (b))) / (sf))"]


let tdivmulinv_upper, tdivmulinv_lower = List.nth rewrites 0

let () = Bound.Log.log_line_s "tdivmulinv upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tdivmulinv_upper
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "tdivmulinv lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tdivmulinv_lower
let () = Bound.Log.log_line_s ""