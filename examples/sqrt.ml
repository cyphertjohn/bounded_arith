open Bound.Expr
open Str

(* let t0 = from_string "x - r0" *)
let t1 = from_string "floor((r0 + floor(x / r0)) / (2)) - r1"
let t2 = from_string "r1 / x - r2"
let tf = from_string "r2 - r"

let vname i = String.concat "" ["r"; (string_of_int i); "m"]
(* let vname i = String.concat "" ["r"; (string_of_int i)] *)

let iter_str r = Str.global_replace (regexp "r0") r "floor(((r0) + floor(x / (r0))) / (2))"

let n = 3

(* ************************************************************************************ *)

(* https://stackoverflow.com/questions/243864/what-is-the-ocaml-idiom-equivalent-to-pythons-range-function *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

let equate s1 s2 = from_string (s1 ^ " - " ^ s2)

let background_theory = [equate (vname n) "res"] @ (List.map (fun cur -> 
																  equate (vname cur) (iter_str (vname (cur - 1)))) 
													   (1--n))
let tupper = Bound.EqRewriter.rewrite background_theory ["x"; (vname 0)] (from_string "x^2 - (res)^2")

(* ************************************************************************************ *)

(* let unrolled_str = ref (vname n)
for i = 0 to n-1 do
	let cur = n-i in
    unrolled_str := global_replace (regexp (vname cur)) (iter_str (vname (cur - 1))) !unrolled_str
done *)

(* let tupper = from_string (Str.global_replace (regexp "res") !unrolled_str "x^2 - (res)^2") *)


(* ************************************************************************************ *)

let tupper_res = Bound.EqRewriter.rewrite [] ["x"; (vname 0)] (Bound.IneqRewriter.rewrite tupper)


(* 
	n=2: "-81/16 + 9/8r - 1/16r^(2) - 5/8x + 9/8r^(-1)x + x^(2) - 1/16r^(-2)x^(2) - 1/4x^(2)(1/2r + 1/2r^(-1)x)^(-2) + 9/4x(1/2r + 1/2r^(-1)x)^(-1)" 
	n=3: "-441/64 + 21/32r - 1/64r^(2) - 21/32x + 21/32r^(-1)x + x^(2) - 1/64r^(-2)x^(2) - 1/16x^(2)(1/2r + 1/2r^(-1)x)^(-2) + 33/16x(1/2r + 1/2r^(-1)x)^(-1) - 1/4x^(2)(1/4r + 1/4r^(-1)x + 1/2x(-3/2 + 1/2r + 1/2r^(-1)x)^(-1))^(-2) + 9/4x(1/4r + 1/4r^(-1)x + 1/2x(-3/2 + 1/2r + 1/2r^(-1)x)^(-1))^(-1)"
*)
