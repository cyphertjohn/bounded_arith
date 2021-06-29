open Mylib.Poly
open Mylib.Sigs

let p1 = Polynomial.from_string "x^2y - 1"
let p2 = Polynomial.from_string "xy^2 - x"
let p3 = Polynomial.from_string "x^3 - 2xy"
let p4 = Polynomial.from_string "x^2y-2y^2+x"

let f1 = Polynomial.from_string "t^2+x^2+y^2+z^2";;
let f2 = Polynomial.from_string "t^2+2x^2-xy-z^2";;
let f3 = Polynomial.from_string "t+y^3-z^3";;

let print_list l = List.iter (fun poly -> print_endline (Polynomial.to_string poly)) l;;

let m1 = Prod [Exp("x", 2)];;
let m2 = Prod [Exp("x", 1);Exp("y",1)];;
let m3 = Prod [Exp("y", 2)];;
let m4 = Prod [Exp("x", 1);Exp("z",1)];;
let m5 = Prod [Exp("y", 1);Exp("z",1)];;
let m6 = Prod [Exp("z", 2)];;

print_list [f1; f2; f3];;