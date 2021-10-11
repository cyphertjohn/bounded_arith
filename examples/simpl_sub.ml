open Bound.Expr
let t1 = from_string "r0 - r1"
let t2 = from_string "x / r1 - r2"
let tf = from_string "r2 - r"
let vars_to_keep = ["x"; "r0"]
let tupper = Bound.EqRewriter.rewrite [t1;t2;tf] [] vars_to_keep (from_string "r")