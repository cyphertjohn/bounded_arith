open Bound.Expr


let y = from_string "y"
let x = from_string "x"
let f1 = func "f" x
let eq1 = minus y f1
let eq2 = from_string "x - 100"


let vars_to_keep = ["x"]
let res = Bound.Rewriter.rewrite [eq1;eq2] [] vars_to_keep [from_string "y"]