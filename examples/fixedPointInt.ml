open Bound.Expr

let vars_to_keep = ["a"; "b"; "sf"]

let tmuldivinv_upper = Bound.EqRewriter.rewrite [] 
												[
												from_string "((floor((a b) / (sf)) sf) / (b)) - floor((floor((a b) / (sf)) sf) / (b))"; (* floor upper bound rule *)
												from_string "((a b) / (sf)) - floor((a b) / (sf))"; (* floor upper bound rule *)
												from_string "sf"; (* input *)
												from_string "1 / b"; (* inverse rule (from input b > 0) *)
												] 
												vars_to_keep (from_string "floor((floor((a b) / (sf)) sf) / (b))")
(* 
utop # to_string tmuldivinv_upper;;
- : string = "a" 
*)

let tmuldivinv_lower = Bound.EqRewriter.rewrite [] 
												[
												from_string "floor((floor((a b) / (sf)) sf) / (b)) + 1 - ((floor((a b) / (sf)) sf) / (b))"; (* floor lower bound rule *)
												from_string "floor((a b) / (sf)) + 1 - ((a b) / (sf))"; (* floor lower bound rule *)
												from_string "sf"; (* input *)
												from_string "1 / b"; (* inverse rule (from input b > 0) *)
												] 
												vars_to_keep (from_string "-floor((floor((a b) / (sf)) sf) / (b))")

(* 
utop # to_string tmuldivinv_lower;;
- : string = "1 - a + b^(-1)sf" 
*)

let tdivmulinv_upper = Bound.EqRewriter.rewrite [] 
												[
												from_string "((b floor((a sf) / (b))) / (sf)) - floor((b floor((a sf) / (b))) / (sf))"; (* floor upper bound rule *)
												from_string "((a sf) / (b)) - floor((a sf) / (b))"; (* floor upper bound rule *)
												from_string "1 / sf"; (* inverse rule (from input sf > 0) *)
												from_string "b"; (* input *)
												] 
												vars_to_keep (from_string "floor((b floor((a sf) / (b))) / (sf))")
(* 
utop # to_string tdivmulinv_upper;;
- : string = "a" 
*)

let tdivmulinv_lower = Bound.EqRewriter.rewrite [] 
												[
												from_string "floor((b floor((a sf) / (b))) / (sf)) + 1 - ((b floor((a sf) / (b))) / (sf))"; (* floor lower bound rule *)
												from_string "floor((a sf) / (b)) + 1 - ((a sf) / (b))"; (* floor lower bound rule *)
												from_string "1 / sf"; (* inverse rule (from input sf > 0) *)
												from_string "b"; (* input *)
												] 
												vars_to_keep (from_string "-floor((b floor((a sf) / (b))) / (sf))")
(* 
utop # to_string tmuldivinv_lower;;
- : string = "1 - a + bsf^-1" 
*)