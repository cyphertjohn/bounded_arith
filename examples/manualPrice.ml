open Bound.Expr

(* priceRange = startPrice - minimumPrice *)
(* timeRange = endTime - startTime *)
let t1 = from_string "floor((priceRange) / (startTime + timeRange)) - drop1"
(* t1diff = t1 - startTime *)
let t2 = from_string "t1diff drop1 - diff1"
let t3 = from_string "startPrice - drop1 - price1"

let vars_to_keep = ["priceRange"; "startTime"; "timeRange"; "t1diff"]

let tupper = Bound.EqRewriter.rewrite [t1;t2;t3] vars_to_keep (from_string "price1 - startPrice")
let tupper_res = Bound.EqRewriter.rewrite [] vars_to_keep (Bound.IneqRewriter.rewrite tupper)