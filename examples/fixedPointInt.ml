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
