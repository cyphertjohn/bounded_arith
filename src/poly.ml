open Mylib.Expr

let t = from_string "1+floor(x-y)"
let t1 = from_string "x- v b /e"
let t2 = from_string "b + a b / e - 1 - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["v"; "a"; "e"]
