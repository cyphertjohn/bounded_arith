open Bound.Expr
open Str

(* let t0 = from_string "x - r0" *)
let t1 = from_string "floor((r0 + floor(x / r0)) / (2)) - r1"
let t2 = from_string "r1 / x - r2"
let tf = from_string "r2 - r"

let vars_to_keep = ["x"; "r0"]

(* let tupper = Bound.EqRewriter.rewrite [t1;t2;tf] vars_to_keep (from_string "x^2 - r^2") *)

let vname i = String.concat "" ["r"; (string_of_int i); "m"]

let iter_str r = Str.global_replace (regexp "r0") r "floor(((r0) + floor(x / (r0))) / (2))"

let n = 2
let unrolled_str = ref (vname n)
for i = 0 to n-1 do
	let cur = n-i in
    unrolled_str := global_replace (regexp (vname cur)) (iter_str (vname (cur - 1))) !unrolled_str
done

let tupper = from_string (Str.global_replace (regexp "res") !unrolled_str "x^2 - (res)^2")

(* *********************** *)

(* let range n = List.init n succ;;    
let tupper2 = Bound.EqRewriter.rewrite
					(List.map (fun i -> String.concat (iter_str (i-1)) " - " (vname i))) (range n)) *)
					


(* *********************** *)

let tupper_res = Bound.EqRewriter.rewrite [] ["x"; (vname 0)] (Bound.IneqRewriter.rewrite tupper)