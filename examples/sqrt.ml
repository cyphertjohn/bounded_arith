open Bound.Expr
open Str

let () = Bound.Log.log_times := true

let vname i = "r" ^ (string_of_int i)

(* https://en.wikipedia.org/wiki/Integer_square_root *)
(* https://dl.acm.org/doi/pdf/10.1145/37523.37525 *)

(* let iter_str r = Str.global_replace (regexp "r0") r "floor(((r0) + floor(x / (r0))) / (2))" *)

(* **************************************************************************** *)

let iter_str r = Str.global_replace (regexp "v") r "floor(((v) + x / (v)) / (2))"

(* **************************************************************************** *)

(* let iter_str r = Str.global_replace (regexp "v") r "(((v) + x / (v)) / (2))" *)

let n = 2

(* ************************************************************************************ *)

(* https://stackoverflow.com/questions/243864/what-is-the-ocaml-idiom-equivalent-to-pythons-range-function *)
let (--) i j = 
    let rec aux n acc =
      if n < i then acc else aux (n-1) (n :: acc)
    in aux j []

let equate s1 s2 = from_string (s1 ^ " - " ^ s2)

let background_theory = [equate (vname n) "res"] @ 
                        (List.map 
                             (fun cur -> equate (vname cur) (iter_str (vname (cur - 1)))) 
													   (1--n)
                        )
                        @ [equate (vname 0) "2"]

let ineq_assumptions = [
                from_string "x";
                from_string (vname 0);
                (* from_string ((vname 0) ^ "^2 - x"); (* initial guess >= sqrt(x) *) *)
                (* from_string ("x - " ^ "("^(vname 0)^"/(2))^2"); (* previous power of 2 is <= sqrt(x) *) *)
                from_string "4 - x";
                from_string "x - 1";
              ] 

let vars_to_keep = ["x"; (vname 0)]
(* let vars_to_keep = ["x";] *)

(* ************************************************************************************ *)

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.Rewriter.rewrite ~sat:5
              background_theory
              ineq_assumptions
              vars_to_keep)
              (from_string "(res - 1)^2 - x")

let tlower = Bound.Log.log_time "Rewrite lower" (Bound.Rewriter.rewrite ~sat:5
              background_theory
              ineq_assumptions
              vars_to_keep)
              (from_string "x - (res + 1)^2")