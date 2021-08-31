open Bound.Expr

(* timeRange = endTime - startTime *)
(* priceRange = startPrice - minimumPrice *)
let t0 = from_string "minimumPrice + priceRange - startPrice"

(* priceRange = startPrice - minimumPrice *)
let t1 = from_string "floor((priceRange) / (startTime + timeRange)) - drop"
(* t1diff = t1 - startTime *)
let t2 = from_string "t1diff drop - diff1"
let t3 = from_string "minimumPrice + priceRange - diff1 - price1"

let vars_to_keep = ["minimumPrice"; "priceRange"; "startTime"; "timeRange"; "t1diff"]

let tupper = Bound.EqRewriter.rewrite [t0;t1;t2;t3] vars_to_keep (from_string "price1 - startPrice")
let tupper_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tupper)

(* utop # to_string tupper;;
- : string = "-t1difffloor(priceRange(startTime + timeRange)^(-1))"
which is negative. But
utop # to_string tupper_res;;
- : string = "t1diff - priceRanget1diff(startTime + timeRange)^(-1)"
might not be. *)

let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] vars_to_keep (from_string "minimumPrice - price1")
let tlower_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tlower)

(* 
utop # to_string tlower;;
- : string =
"-priceRange + t1difffloor(priceRange(startTime + timeRange)^(-1))"
utop # to_string tlower_res;;
- : string = "-priceRange + priceRanget1diff(startTime + timeRange)^(-1)"
Negative only when t1diff <= timeRange! 
(in which case t1diff(startTime + timeRange) < 1 and hence priceRange times this is less than priceRange)
*)

let t0_2 = from_string "t1diff + telapsed - t2diff"
let t2_2 = from_string "t2diff drop - diff2"
let t3_2 = from_string "minimumPrice + priceRange - diff2 - price2"

let vars_to_keep_2 = "telapsed" :: vars_to_keep

let tmonotone = Bound.EqRewriter.rewrite [t0;t1;t2;t3;t0_2;t2_2;t3_2] vars_to_keep_2 (from_string "price2 - price1")
let tmonotone_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tmonotone)
(*
utop # to_string tmonotone;;
- : string = "-telapsedfloor(priceRange(startTime + timeRange)^(-1))"
utop # to_string tmonotone_res;;
- : string = "telapsed - priceRangetelapsed(startTime + timeRange)^(-1)"
Similar to the issue with tupper.
*)