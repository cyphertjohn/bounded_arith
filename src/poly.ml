open Mylib.Expr

let p1 = from_string "x^2y - 1"
let p2 = from_string "xy^2 - x"
let p3 = from_string "x^3 - 2xy"
let p4 = from_string "x^2y-2y^2+x"

let print_list l = List.iter (fun poly -> print_endline (to_string poly)) l;;

print_list [p1; p2; p3];;