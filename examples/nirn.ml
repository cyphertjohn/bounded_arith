open Bound.Expr
open SymBoundBenchmark

let () = Bound.Log.log_times := true

let () = SymBoundBenchmark.process_cmdline ()
let sat_bound = SymBoundBenchmark.sat_bound ()
let use_proj = not (SymBoundBenchmark.use_lp ())

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

let tupperAndTlower = Bound.Log.log_time "Rewrite total" (Bound.Rewriter.rewrite ~use_proj:use_proj ~sat:sat_bound (transferX @ transferYAfterX @ [from_string "10^2 - E18"])
						  (List.map from_string ["supply0 - 1" (* shares = supply == 0 ? amount : amount.mul(supply) / bal *); 
						  						(* "priceAtLastFee0"; *) 
						  						"performanceFee"; 
						  						"balance"; 
						  						"x"; 
						  						(* "E18";  *)
						  						"balance - valueAtLastCollectionPriceY"; (* if (totalBalance <= valueAtLastCollectionPrice) return 0; *)
						  						"balance - feesY"; (* totalBalance.sub(totalFees); see https://docs.openzeppelin.com/contracts/2.x/api/math#SafeMath-sub-uint256-uint256- *)
						  					])
						  vars_to_keep)
   						  [(from_string "sharesX - sharesY")]

let () = Bound.Log.log_line_s "sharesX - sharesY upper bounds"
let () = List.iter (fun u -> Bound.Log.log pp (Some u)) (fst (List.hd tupperAndTlower))
let () = Bound.Log.log_line_s ""

let () = Bound.Log.log_line_s "sharesX - sharesY lower bounds"
let () = List.iter (fun l -> Bound.Log.log pp (Some l)) (snd (List.hd tupperAndTlower))