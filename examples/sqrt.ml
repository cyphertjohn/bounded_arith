open Bound.Expr

let t0 = from_string "x - r0"
let t1 = from_string "floor(floor(r0 + x / r0) / 2) - r1"
let t2 = from_string "floor(floor(r1 + x / r1) / 2) - r2"
let tf = from_string "r3 - r"

let vars_to_keep = ["x"; "r0"]

let tupper = Bound.EqRewriter.rewrite [t0;t1;t2;tf] vars_to_keep (from_string "x^2 - r^2")
let tupper_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tupper)