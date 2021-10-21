open Bound.Expr

let t1 = from_string "x - v b /e"
let t2 = from_string "b + floor(a b / e) - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["v"; "a"; "e"; "b";]

(* 79.571205s *)
(* let tupper = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "x - floor(x)";
									  	from_string "floor(y) + 1 - y";
									  	from_string "floor(a b / e) + 1 - (a b / e)";
									  	from_string "v";
									  	from_string "1/(e + a)";
									  ] 
									  vars_to_keep 
									  (from_string "floor(x) - floor(y)") *)

(* result "1". 65.898197s *)
let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
										from_string "floor(x) + 1 - x";
									  	from_string "y - floor(y)";
									  	from_string "(a b / e) - floor(a b / e)";
									  	from_string "v";
									  	from_string "1/(e + a)";
									  ] 
									  vars_to_keep 
									  (from_string "floor(y) - floor(x)")

(* result "-floor(be^-1v) + floor(b(a + e)^-1v + (a + e)^-1vfloor(abe^-1))". 3.372992s 
The reason is that the derivation in the writeup performs inequational reasoning under the floor term,
which is impossible in the cone. *)
(* let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "(a b / e) - floor(a b / e)";
									  	from_string "v";
									  	from_string "1/(e + a)";
									  ] 
									  vars_to_keep 
									  (from_string "floor(y) - floor(x)") *)