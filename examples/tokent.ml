open Bound.Expr

let () = Bound.Log.log_times := true

let vars_to_keep = ["x"; "supply0"; "balance0"; "liquidFunds"]

let withdrawSplit = List.map from_string [
					(* withdraw x *)
					"floor(x * liquidFunds / supply0) - amountSplit1";
					"balance0 - x - balance1Burn";
					"supply0 - x - supply1";
					"balance1Burn - amountSplit1 - balance1Withdrawn";
					(* withdraw x *)
					"floor(x * liquidFunds / supply1) - amountSplit2";
					"balance1Withdrawn - x - balance2Burn";
					(* "supply1 - x - supply2"; *)
					"balance2Burn - amountSplit2 - balanceSplit";
				] 
let withdrawJoined = List.map from_string [
					"floor((x * 2) * liquidFunds / supply0) - amountJoined";
					"balance0 - (x * 2) - balanceJoinedBurn";
					(* "supply0 - (x * 2) - supply1"; *)
					"balanceJoinedBurn - amountJoined - balanceJoined";
				]

let tupperAndTlower = Bound.Log.log_time "Rewrite joined no worse" (Bound.Rewriter.rewrite ~sat:3 (withdrawSplit @ withdrawJoined)
						  (List.map from_string ["x"; "supply0 - 2x"; "balance0 - 2x"; "liquidFunds"])
						  vars_to_keep)
   						  [from_string "balanceSplit - balanceJoined"]