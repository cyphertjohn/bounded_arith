open Bound.Expr

let () = Bound.Log.log_times := true

let vars_to_keep = ["supply0"; "priceAtLastFee0"; "performanceFee"; "totalBalance0"; "x"; "y"; "E18"]

let transferX = List.map from_string [
					(** transfer x **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
						(* "floor(supply0 priceAtLastFee0 / E18)  - valueAtLastCollectionPriceX"; *)
						(* "floor((totalBalance0 - valueAtLastCollectionPriceX) performanceFee) - totalFeesX"; *)
						(* "floor(totalFeesX supply0 / (totalBalance0 - totalFeesX)) - equivalentSharesX"; *)
						(* mint *)
							(* "supply0 + equivalentSharesX - supplyXmid"; *)
							"totalBalance0 - totalBalanceXmid"; (* "totalBalance0 + equivalentSharesX - totalBalanceXmid"; *)
						(* rest of calculate fee *)
						(* "floor((totalBalance0 E18) / (supplyXmid)) - priceAtLastFeeX"; *)
					(* rest of transfer x *)
					(* "floor((x supplyXmid) / (totalBalanceXmid)) - sharesX"; *)
					(* mint *)
						(* "supplyXmid + sharesX - supplyX"; *)
						"totalBalanceXmid - totalBalanceX"; (* "totalBalanceXmid + sharesX - totalBalanceX"; *)
				] 
let transferYAfterX = List.map from_string [
					(** transfer y **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
						(* "floor(supplyX priceAtLastFeeX / E18)  - valueAtLastCollectionPriceY"; *)
						(* "floor((totalBalanceX - valueAtLastCollectionPriceY) performanceFee) - totalFeesY"; *)
						(* "floor(totalFeesY supplyX / (totalBalanceX - totalFeesY)) - equivalentSharesY"; *)
						(* mint *)
							(* "supplyX + equivalentSharesY - supplyYmid"; *)
							"totalBalanceX - totalBalanceYmid"; (* "totalBalanceX + equivalentSharesY - totalBalanceYmid"; *)
						(* rest of calculate fee *)
						(* "floor((totalBalanceX E18) / (supplyYmid)) - priceAtLastFeeY"; *)
					(* rest of transfer y *)
					(* "floor((y supplyYmid) / (totalBalanceYmid)) - sharesY"; *)
					(* mint *)
						(* "supplyYmid + sharesY - supplyY"; *)
						"totalBalanceYmid - totalBalanceY"; (* "totalBalanceYmid + sharesY - totalBalanceY"; *)
				] 
let transferXplusY = List.map from_string [
					(** transfer x + y **)
					(* transfer from - ignored. total balance remains the same. *)
					(* calculate fee *)
						(* "floor(supply0 priceAtLastFee0 / E18)  - valueAtLastCollectionPriceXY"; *)
						(* "floor((totalBalance0 - valueAtLastCollectionPriceXY) performanceFee) - totalFeesXY"; *)
						(* "floor(totalFeesX supply0 / (totalBalance0 - totalFeesXY)) - equivalentSharesXY"; *)
						(* mint *)
							(* "supply0 + equivalentSharesXY - supplyXYmid"; *)
							"totalBalance0 - totalBalanceXYmid"; (* "totalBalance0 + equivalentSharesXY - totalBalanceXYmid"; *)
						(* rest of calculate fee *)
						(* "floor((totalBalance0 E18) / (supplyXYmid)) - priceAtLastFeeXY"; *)
					(* rest of transfer x + y *)
					(* "floor(((x+y) supplyXYmid) / (totalBalanceXYmid)) - sharesXY"; *)
					(* mint *)
						(* "supplyXYmid + sharesXY - supplyXY"; *)
						"totalBalanceXYmid - totalBalanceXY"; (* "totalBalanceXYmid + sharesXY - totalBalanceXY"; *)
				] 

let tupper = Bound.Log.log_time "Rewrite upper" (Bound.EqRewriter.rewrite (transferX @ transferYAfterX @ transferXplusY)
						  [] 
						  vars_to_keep)
   						  (from_string "totalBalanceXY - totalBalanceY")