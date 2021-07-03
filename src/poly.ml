open Mylib.Expr

let t = from_string "a2-floor(a*b/e)"
let t1 = from_string "e1 - e - a"
let t2 = from_string "b1 - b - a2"
let t3 = from_string "floor(v*b/e) - floor(v*b1/e1)"

let vars_to_keep = ["v"; "a"; "e"; "b"]

(*let (polys, term_map) = Mylib.EqRewriter.rewrite [t;t1;t2;t3] vars_to_keep*)