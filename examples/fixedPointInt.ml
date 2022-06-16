open Bound.Expr

let vars_to_keep = ["a"; "b"; "sf"]

let () = Bound.Log.log_times := true

let rewrites = Bound.Log.log_time "Rewrite mult/div upper" (Bound.Rewriter.rewrite ~sat:3 [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  [from_string "floor((floor((a b) / (sf)) sf) / (b))";
									   from_string "floor((b floor((a sf) / (b))) / (sf))"]


let tmuldivinv_upper, tmuldivinv_lower = List.nth rewrites 0
let tdivmulinv_upper, tdivmulinv_lower = List.nth rewrites 1

let () = Bound.Log.log_line_s "tmuldivinv upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tmuldivinv_upper
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "tmuldivinv lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tmuldivinv_lower
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "tdivmulinv upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tdivmulinv_upper
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "tdivmulinv lower bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tdivmulinv_lower
let () = Bound.Log.log_line_s ""