open Bound.Expr

let () = Bound.Log.log_times := true

let vars_to_keep = ["x"; "supply0"; "balance0"]

let withdrawSplit = List.map from_string [
					"floor(x * balance0 / supply0) - amountSplit1";
					"balance0 - amountSplit1 - balance1";
					"floor(x * balance1 / supply0) - amountSplit2";
					"balance1 - amountSplit2 - balanceSplit";
					"balance2 - resSplit"
				] 
let withdrawJoined = List.map from_string [
					"floor((x * 2) * balance0 / supply0) - amountJoined";
					"balance0 - amountJoined - balanceJoined";
				]

let tupper = Bound.Log.log_time "Rewrite joined no worse" (Bound.Rewriter.rewrite ~sat:4 (withdrawSplit @ withdrawJoined)
						  (List.map from_string ["x"; "supply0"; "balance0"])
						  vars_to_keep)
   						  (from_string "balanceSplit - balanceJoined")