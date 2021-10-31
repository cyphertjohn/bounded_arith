open Bound.Expr

let vars_to_keep = ["a"; "b"; "sf"]

let tmuldivinv_upper = Bound.Log.log_time "Rewrite mult/div upper" (Bound.EqRewriter.rewrite [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  (from_string "floor((floor((a b) / (sf)) sf) / (b))")
(* 
utop # to_string tmuldivinv_upper;;
- : string = "a" 
*)

let tmuldivinv_lower = Bound.Log.log_time "Rewrite mult/div lower" (Bound.EqRewriter.rewrite [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  (from_string "-floor((floor((a b) / (sf)) sf) / (b))")
(* 
utop # to_string tmuldivinv_lower;;
- : string = "1 - a + b^(-1)sf" 
*)

let tdivmulinv_upper = Bound.Log.log_time "Rewrite div/mult upper" (Bound.EqRewriter.rewrite [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  (from_string "floor((b floor((a sf) / (b))) / (sf))")
(* 
utop # to_string tdivmulinv_upper;;
- : string = "a" 
*)

let tdivmulinv_lower = Bound.Log.log_time "Rewrite div/mult lower" (Bound.EqRewriter.rewrite [] 
									  [
										from_string "sf";
										from_string "b";
									  ] 
									  vars_to_keep)
									  (from_string "-floor((b floor((a sf) / (b))) / (sf))")
(* 
utop # to_string tmuldivinv_lower;;
- : string = "1 - a + bsf^-1" 
*)