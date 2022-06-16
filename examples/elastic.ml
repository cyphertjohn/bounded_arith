open Bound.Expr

(*let t1 = from_string "x - v b /e"
let t2 = from_string "b + floor(a b / e) - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["v"; "a"; "e"; "b"]

let () = Bound.Log.log_times := true

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.EqRewriter.rewrite [t1;t2;t3] 
						  [
							from_string "v";
						  	from_string "e";
  						  	from_string "a";
						  ] 
						  vars_to_keep)
   						  (from_string "floor(x) - floor(y)")

let tlower = Bound.Log.log_time "Rewrite lower" (Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "v";
									  	from_string "e";
										from_string "a"
									  ] 
									  vars_to_keep) (from_string "floor(y) - floor(x)")


*)

let t1 = from_string "x - floor(v b /e)"
let t2 = from_string "a2 - floor(a b / e)"
let t3 = from_string "ep - e - a"
let t4 = from_string "bp - b - a2"
let t5 = from_string "y - floor(v bp / ep)"

let vars_to_keep = ["v"; "a"; "e"; "b"]

let () = Bound.Log.log_times := true

let ts = Bound.Log.log_time "Rewrite upper" (Bound.Rewriter.rewrite ~sat:3 [t1;t2;t3;t4;t5] 
						  [
							from_string "v";
						  	from_string "e";
  						  	from_string "a";
						  ] 
						  vars_to_keep)
   						  [from_string "x - y"]

let tuppers, tlowers = List.hd ts

let () = Bound.Log.log_line_s "t upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) tuppers
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "t lower bounds"
let () = List.iter (fun l -> Bound.Log.log pp (Some l)) tlowers

