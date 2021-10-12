open Bound.Expr

let t0 = from_string "x - a"
let vars_to_keep = ["x"; "a"]
let res = Bound.EqRewriter.rewrite [] [t0] vars_to_keep (from_string "-x")