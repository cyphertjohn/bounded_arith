open Bound.Expr

let vars_to_keep = ["a"; "b"; "sf"]

let tmuldivinv_upper = Bound.EqRewriter.rewrite [] [] vars_to_keep (from_string "floor((floor((a b) / (sf)) sf) / (b)) - a")
let tmuldivinv_upper_res = Bound.EqRewriter.rewrite [] [] vars_to_keep (Bound.IneqRewriter.rewrite tmuldivinv_upper)
(* 
utop # to_string tmuldivinv_upper_res;;
- : string = "0" 
*)

let tmuldivinv_lower = Bound.EqRewriter.rewrite [] [] vars_to_keep (from_string "a - floor((floor((a b) / (sf)) sf) / (b))")
let tmuldivinv_lower_res = Bound.EqRewriter.rewrite [] [] vars_to_keep (Bound.IneqRewriter.rewrite tmuldivinv_lower)
(* 
utop # to_string tmuldivinv_lower_res;;
- : string = "1 + b^(-1)sf" 
*)


let tdivmulinv_upper = Bound.EqRewriter.rewrite [] [] vars_to_keep (from_string "floor((b floor((a sf) / (b))) / (sf)) - a")
let tdivmulinv_upper_res = Bound.EqRewriter.rewrite [] [] vars_to_keep (Bound.IneqRewriter.rewrite tdivmulinv_upper)
(* 
utop # to_string tdivmulinv_res;;
- : string = "0" 
*)

let tdivmulinv_lower = Bound.EqRewriter.rewrite [] [] vars_to_keep (from_string "a - floor((b floor((a sf) / (b))) / (sf))")
let tdivmulinv_lower_res = Bound.EqRewriter.rewrite [] [] vars_to_keep (Bound.IneqRewriter.rewrite tdivmulinv_lower)