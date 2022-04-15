open Bound.Expr

let vars_to_keep = ["a"; "b"; "sf"]

let rewrites = Bound.Log.log_time "Rewrite mult/div upper" (Bound.Rewriter.rewrite [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  [from_string "floor((floor((a b) / (sf)) sf) / (b))";
									   from_string "-floor((floor((a b) / (sf)) sf) / (b))";
									   from_string "floor((b floor((a sf) / (b))) / (sf))";
									   from_string "-floor((b floor((a sf) / (b))) / (sf))"]


let tmuldivinv_upper = List.nth rewrites 0
let tmuldivinv_lower = List.nth rewrites 1
let tdivmulinv_upper = List.nth rewrites 2
let tdivmulinv_lower = List.nth rewrites 3
