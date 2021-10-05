open Bound.Expr
open Str

let vname i = String.concat "" ["r"; (string_of_int i); "m"]

let iter_str r = Str.global_replace (regexp "r0") r "floor(((r0) + floor(x / (r0))) / (2))"

let n = 4

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
let tupper = Bound.EqRewriter.rewrite background_theory [] ["x"; (vname 0)] (from_string "x - (res)^2")
(* let tlower = Bound.EqRewriter.rewrite background_theory ["x"; (vname 0)] (from_string "(res)^2 - x") *)

(* ************************************************************************************ *)

let tupper_res = Bound.EqRewriter.rewrite [] [] ["x"; (vname 0)] (Bound.IneqRewriter.rewrite tupper)
(* let tlower_res = Bound.EqRewriter.rewrite [] ["x"; (vname 0)] (Bound.IneqRewriter.rewrite tlower) *)

let p = to_string tupper_res