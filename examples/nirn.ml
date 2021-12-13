open Bound.Expr

let t1 = from_string "bx0 - x - bx1"
let t2_+

let t1 = from_string "x - v b /e"
let t2 = from_string "b + floor(a b / e) - z"
let t3 = from_string "y - v z/(e+a)"

let vars_to_keep = ["supply0"; "priceAtLastFee0"; "performanceFee"; "totalBalance0"; "x"; "y"; "E18"]

let () = Bound.Log.log_times := true

let transferX = [
					(** transfer x **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
						"floor(supply0 priceAtLastFee0 / E18)  - valueAtLastCollectionPriceX";
						"floor((totalBalance0 - valueAtLastCollectionPriceX) performanceFee) - totalFeesX";
						"floor(totalFeesX supply0 / (totalBalance0 - totalFeesX)) - equivalentSharesX";
						(* mint *)
							"supply0 + equivalentSharesX - supplyXmid";
							"totalBalance0 - totalBalanceXmid"; (* "totalBalance0 + equivalentSharesX - totalBalanceXmid"; *)
						(* rest of calculate fee *)
						"floor(totalBalance0 * E18) - priceAtLastFeeX";
					(* rest of transfer x *)
					"floor((x * supplyX) / totalBalanceXmid - sharesX";
					(* mint *)
						"supplyXmid + sharesX - supplyX";
						"totalBalanceXmid - totalBalanceX"; (* "totalBalanceXmid + sharesX - totalBalanceX"; *)
				] 
let transferYafterX = 
				[
					(** transfer y **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
					"floor(supplyX priceAtLastFeeX / E18)  - valueAtLastCollectionPriceY";
					"floor((totalBalanceX - valueAtLastCollectionPriceY) performanceFee) - totalFeesY";
					"floor(totalFeesY supplyX / (totalBalanceX - totalFeesY)) - equivalentSharesY";
					(* mint *)
					"supplyX + equivalentSharesY - supplyY";
					"totalBalanceX - totalBalanceY"; (* "totalBalanceX + equivalentSharesY - totalBalanceY"; *)
					(* rest of calculate fee *)
					"floor(totalBalanceX * E18) - priceAtLastFeeY";
				] 
let transferXplusY = 
				[
					(** transfer x+y **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
					"floor(supply0 priceAtLastFee0 / E18)  - valueAtLastCollectionPriceXY";
					"floor((totalBalance0 - valueAtLastCollectionPriceXY) performanceFee) - totalFeesXY";
					"floor(totalFeesXY supply0 / (totalBalance0 - totalFeesXY)) - equivalentSharesXY";
					(* mint *)
					"supply0 + equivalentSharesXY - supplyXY";
					"totalBalance0 - totalBalanceXY"; (* "totalBalance0 + equivalentSharesXY - totalBalanceXY"; *)
					(* rest of calculate fee *)
					"floor(totalBalance0 * E18) - priceAtLastFeeXY";
				] 

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.EqRewriter.rewrite 
						  [
							from_string "v";
						  	from_string "e";
  						  	from_string "a";
						  ] 
						  vars_to_keep)
   						  (from_string "floor(x) - floor(y)")