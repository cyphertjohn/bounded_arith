open Bound.Expr

let t1 = from_string "x - v b /e"
let t2 = from_string "b + floor(a b / e) - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["v"; "a"; "e"; "b";]

let tupper = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "floor(x - y) - (floor(x) - floor(y))";
									  	(* from_string "x - floor(x)";  *)(* from_string "y - floor(y)"; *)
									  	(* from_string "floor(x) + 1 - x"; *) from_string "floor(y) + 1 - y";
									  	(* from_string "(a b / e) - floor(a b / e)";  *) from_string "floor(a b / e) + 1 - (a b / e)";
									  	from_string "v";
									  	(* from_string "a";
									  	from_string "e";
									  	from_string "b"; *)
									  	from_string "1/(e + a)";
									  	from_string "b e / v - floor(b e / v)"
									  ] 
									  vars_to_keep 
									  (from_string "floor(x) - floor(y)")

(* let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] [] vars_to_keep (from_string "floor(y) - floor(x)") *)