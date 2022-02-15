open Bound.Expr

let () = Bound.Log.log_times := true

let vars_to_keep = ["supply0"; (* "priceAtLastFee0"; *) "performanceFee"; "balance"; "x"; (* "y"; *) "E18"]

let transferX = List.map from_string [
					(* "balance - valueAtLastCollectionPriceX";
					"balance - valueAtLastCollectionPriceX - profitX";
					"floor(profitX * performanceFee / E18) - feesX";
					"floor(feesX * supply0 / (balance - feesX)) - equivalentSharesX"; *)
					"supply0 - supplyX";
					"floor((x * supplyX) / (balance)) - sharesX";

					"floor(balance * E18 / supplyX) - priceAtLastFeeX";
				] 
let transferYAfterX = List.map from_string [
					"floor(supplyX * priceAtLastFeeX / E18) - valueAtLastCollectionPriceY"; (* "balance - valueAtLastCollectionPriceY"; *)
					"balance - valueAtLastCollectionPriceY - profitY";
					"floor(profitY * performanceFee / E18) - feesY";
					"floor(feesY * supplyX / (balance - feesY)) - equivalentSharesY";
					"supplyX + equivalentSharesY - supplyY";
					"floor((x * supplyY) / (balance)) - sharesY";
				]

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.EqRewriter.rewrite ~sat:3 (transferX @ transferYAfterX @ [from_string "10^2 - E18"])
						  (List.map from_string ["supply0"; (* "priceAtLastFee0"; *) "performanceFee"; "balance"; "x"; "E18"])
						  vars_to_keep)
   						  (from_string "sharesX - sharesY")

let tlower = Bound.Log.log_time "Rewrite lower" (Bound.EqRewriter.rewrite ~sat:3 (transferX @ transferYAfterX @ [from_string "10^2 - E18"])
						  (List.map from_string ["supply0"; (* "priceAtLastFee0"; *) "performanceFee"; "balance"; "x"; "E18"])
						  vars_to_keep)
   						  (from_string "sharesY - sharesX")