open Sigs.Expr

let rec expr_sign expr =
	match expr with
	| Coe x -> Sigs.Q.sgn x
	| Var _ -> 1
	| Pow (base, exponent) ->
		let base_sign = expr_sign base in
		if base_sign >= 0 then base_sign 
			else if exponent mod 2 = 0 then 1 else -1
	| Mult prod_list -> (List.fold_left (fun x y -> x * y) 1 (List.map expr_sign prod_list))
	| Add sum_list -> 
		(* TODO: not handling simplifications *)
		let sum_signs = List.map expr_sign sum_list in
		if 		(List.fold_left (&&) true (List.map (fun s -> s >= 0) sum_signs)) then 1 (* +a_1 + a_2 + ...*)
		else if (List.fold_left (&&) true (List.map (fun s -> s <= 0) sum_signs)) then -1 (* -a_1 - a_2 - ...*)
		else failwith "inconclusive sign due to mixed sign addition"
	| Div (num, denom) -> (expr_sign num) * (expr_sign denom)
	| Floor x -> expr_sign x

let rewrite (t: Sigs.Q.coef Sigs.Expr.expr): Sigs.Q.coef Sigs.Expr.expr = 
	let rec elim_floor expr polarity =
		match expr with
  		| Coe _ | Var _ -> expr
  		| Pow (base, exponent) ->
  			let new_polarity = polarity <> (exponent < 0) in
  			let rewritten_base = elim_floor base new_polarity in
    		Pow (rewritten_base, exponent)
  		| Mult prod_list -> 
  			let total_sign = expr_sign expr in
  			let new_polarity a = 
  				if total_sign * (expr_sign a) >= 0 then
  					polarity
  				else
  					not polarity
  				in
    		Mult (List.map (fun a -> elim_floor a (new_polarity a)) prod_list) 
  		| Add sum_list ->
    		Add (List.map (fun a -> elim_floor a polarity) sum_list)
  		| Div (num, denom) ->
  			Div (elim_floor num polarity, elim_floor denom (not polarity))
  		| Floor x -> 
  			let nx = elim_floor x polarity in
  			if polarity then nx else Add [nx; (Coe (Sigs.Q.from_string_c "-1"))]
    in elim_floor t true