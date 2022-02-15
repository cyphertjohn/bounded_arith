open Bound.Expr

let () = Bound.Log.log_times := true

let vars_to_keep = ["supply0"; (* "priceAtLastFee0"; *) "performanceFee"; "balance"; "x"; (* "y"; *) "E18"]

let transferX = List.map from_string [
					(* "balance - valueAtLastCollectionPriceX";
					"balance - valueAtLastCollectionPriceX - profitX";
					"floor(profitX * performanceFee / E18) - feesX";
					"floor(feesX * supply0 / (balance - feesX)) - equivalentSharesX"; *)
					(* "supply0 - supplyX"; *)
					"floor((x * supply0) / (balance)) - sharesX";

					"floor(balance * E18 / supply0) - priceAtLastFeeX";
				] 
let transferYAfterX = List.map from_string [
					(* "floor(supply0 * priceAtLastFeeX / E18) - valueAtLastCollectionPriceY"; (* "balance - valueAtLastCollectionPriceY"; *) *)
					(* "balance - (floor(supply0 * priceAtLastFeeX / E18)) - profitY"; *)
					"floor((balance - (floor(supply0 * priceAtLastFeeX / E18))) * performanceFee / E18) - feesY";
					"floor(feesY * supply0 / (balance - feesY)) - equivalentSharesY";
					"supply0 + equivalentSharesY - supplyY";
					"floor((x * supplyY) / (balance)) - sharesY";
				]

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.EqRewriter.rewrite ~sat:3 (transferX @ transferYAfterX)
						  (List.map from_string ["supply0"; (* "priceAtLastFee0"; *) "performanceFee"; "balance"; "x"; "E18"])
						  vars_to_keep)
   						  (from_string "sharesX - sharesY")