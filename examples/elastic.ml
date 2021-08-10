open Bound.Expr

let t1 = from_string "x - v b /e"
let t2 = from_string "b + floor(a b / e) - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["v"; "a"; "e"; "b"]

let tupper = Bound.EqRewriter.rewrite [t1;t2;t3] vars_to_keep (from_string "floor(x) - floor(y)")
let tupper_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tupper)

let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] vars_to_keep (from_string "floor(y) - floor(x)")
let tlower_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tlower)