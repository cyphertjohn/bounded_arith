open Sigs.Expr

let rec cmp a b = 
  match (a, b) with
  | (Coe a_v, Coe b_v) ->		(* O-1 *)
    compare a_v b_v
  | (Var x, Var y) -> compare x y
  | (Add a_list, Add b_list) | (Mult a_list, Mult b_list) ->
    let a_rev = List.rev a_list in
    let b_rev = List.rev b_list in
    let rec aux x y = 
    (match (x, y) with
    | ([], []) -> 0		(* the two lists are equal *)
    | ([], _) -> (-1)		(* n>m *)	(* O-3-3 *)
    | (_, []) -> 1		(* m>n *)	(* O-3-3 *)
    | (x_hd :: x_rest, y_hd :: y_rest) ->
      if (cmp x_hd y_hd) = 0 then aux x_rest y_rest	(* O-3-2 *)
      else cmp x_hd y_hd		(* O-3-1 *)
    ) in aux a_rev b_rev
  | (Pow (a_bas, a_exp), Pow (b_bas, b_exp)) ->
    if (cmp a_bas b_bas) <> 0 then				(* O-4-1 *)
      cmp a_bas b_bas
    else compare a_exp b_exp			(* O-4-2 *)
  | (Floor x, Floor y) ->
    cmp x y
  | (Div (xn, xd), _) ->
    cmp (Mult [xn; Pow(xd, -1)]) b
  | (_, Div (yn, yd)) ->
    cmp a (Mult [yn; Pow (yd, -1)])
  | (Coe _, _) -> (-1)				(* O-7 *)
  | (_, Coe _) -> (1)
  | (Mult _, _) ->
    cmp a (Mult [b])			(* O-8 *)
  | ( _, Mult _)  ->	
    cmp (Mult [a]) b			(* O-8 *)
  | (Pow _, _) ->
    cmp a (Pow (b, 1))	(* O-9 *)
  | (_, Pow _) ->
    cmp (Pow (a, 1)) b	(* O-9 *)
  | (Floor _, _) -> 1
  | (_, Floor _) -> (-1)
  | (Add _, _) ->
    cmp a (Add [b])				(* O-10 *)
  | (_, Add _) ->
    cmp (Add [a]) b				(* O-10 *)

let base expr = 
  match expr with
  | Pow (base, _) ->
    base
  | _ ->
    expr
     
let exponent expr = 
  match expr with
  | Pow (_, exp) ->
    exp
  | _ ->
    1
    
let term expr = 
  match expr with
  | Mult ((Coe _) :: tail :: []) ->
    Some tail
  | Mult ((Coe _) :: rest) ->
    Some (Mult rest)
  | Mult lis ->
    Some (Mult lis)
  | Coe _ ->
    None
  | _ ->
    Some expr
    
let const expr = 
  match expr with
  | Mult ((Coe rat) :: _) ->
    rat
  | Coe rat ->
    rat
  | _ ->
    Sigs.Q.from_string_c "1"

(* input list size is >= 2 *)
let rec simplify_sum_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
      (match (u_1, u_2) with
      | (Add p, Add q) ->	(* SPRDREC-2-1 *)
        merge_sums p q
      | (Add p, _) ->		(* SPRDREC-2-2 *)
        merge_sums p (u_2 :: [])
      | (_, Add q) ->		(* SPRDREC-2-3 *)
        merge_sums (u_1 :: []) q
      | (Coe v_1, Coe v_2) ->	(* SPRDREC-1-1 *)
        let s = Sigs.Q.addc v_1 v_2 in
        if Sigs.Q.is_zero s then []
        else (Coe (Sigs.Q.addc v_1 v_2)) :: []
      | (Coe v_1, _) when Sigs.Q.is_zero v_1 ->	(* SPRDREC-1-2-a *)
          u_2 :: []
      | (_, Coe v_2) when Sigs.Q.is_zero v_2 ->	(* SPRDREC-1-2-b *)
          u_1 :: []
      | _ ->
          let u_1_term = term u_1 in
          let u_1_const = const u_1 in
          let u_2_term = term u_2 in
          let u_2_const = const u_2 in
          match (u_1_term, u_2_term) with
          | None, Some _ | Some _, None ->
            if (cmp u_2 u_1) < 0 then u_2 :: u_1 :: []		(* SPRDREC-1-4 *)
            else expr_list
          | Some u_1_t, Some u_2_t when (cmp u_1_t u_2_t <> 0) -> 
            if (cmp u_2 u_1) < 0 then u_2 :: u_1 :: []		(* SPRDREC-1-4 *)
            else expr_list
          | Some u_1_t, Some _ -> 
            let s = Sigs.Q.addc u_1_const u_2_const in (* SPRDREC-1-3 *)
            let p = simplify_product (Coe s :: u_1_t :: []) in
            (match p with 
            | Coe rat when Sigs.Q.is_zero rat -> []
            | _ -> (p :: []))
          | None, None ->
            let s = Sigs.Q.addc u_1_const u_2_const in
            if Sigs.Q.is_zero s then []
            else (Coe s) :: []
      )
  | u_1 :: rest ->
      let w = simplify_sum_rec rest in
      (match u_1 with
      | Add p ->						(* SPRDREC-3-1 *)
          merge_sums p w
      | _ ->
          merge_sums (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | _ ->
      failwith "Error in simplify sum rec"

and merge_sums p q = 
  match (p, q) with
  | (_, []) -> p	(* MRSM-1 *)
  | ([], _) -> q	(* MRSM-2 *)
  | (p1 :: rest_p, q1 :: rest_q) ->
      let h = simplify_sum_rec (p1 :: q1 :: []) in
      (match h with
      | [] -> merge_sums rest_p rest_q	(* MRSM-3-1 *)
      | h1 :: [] -> h1 :: (merge_sums rest_p rest_q)	(* MRSM-3-2 *)
      | _ ->
           if h = (p1 :: q1 :: []) then List.append (p1 :: []) (merge_sums rest_p q)	(* MRSM-3-3 *)
           else if h = (q1 :: p1 :: []) then List.append (q1 :: []) (merge_sums p rest_q)	(* MRSM-3-4 *)
           else failwith "Error in merge_sums"
      )

and simplify_sum expr_list = 
  match expr_list with
  | [] -> Coe (Sigs.Q.from_string_c "0")
  | u_1 :: [] -> u_1		
  | _ ->
    let simp_list = simplify_sum_rec expr_list in 
    (match simp_list with 	
    | [] -> Coe (Sigs.Q.from_string_c "0")
    | v_1 :: [] -> v_1
    | _ -> Add simp_list
    )
      
  
(* input list size is >= 2 *)
and simplify_product_rec expr_list = 
  match expr_list with
  | u_1 :: u_2 :: [] ->
    (match (u_1, u_2) with
    | (Mult p, Mult q) ->	(* SPRDREC-2-1 *)
      merge_products p q
    | (Mult p, _) ->		(* SPRDREC-2-2 *)
      merge_products p (u_2 :: [])
    | (_, Mult q) ->		(* SPRDREC-2-3 *)
      merge_products (u_1 :: []) q
    | (Coe v_1, Coe v_2) ->	(* SPRDREC-1-1 *)
      let result = Sigs.Q.mulc v_1 v_2 in
      (if Sigs.Q.is_one result then
        []
      else (Coe result) :: [] )
    | (Coe v_1, _) when (Sigs.Q.is_one v_1) ->	(* SPRDREC-1-2-a *)
      u_2 :: []
    | (_, Coe v_2) when (Sigs.Q.is_one v_2) ->	(* SPRDREC-1-2-b *)
      u_1 :: []
    | _ ->							(* SPRDREC-1-3 *)
      let u_1base = base u_1 in
      let u_1exp = exponent u_1 in
      let u_2base = base u_2 in
      let u_2exp = exponent u_2 in
      if (cmp u_1base u_2base) = 0 then
        let s = u_1exp + u_2exp in 
        let p = simplify_power u_1base s in
        (match p with 
        | Coe rat when Sigs.Q.is_one rat -> []
        | _ -> (p :: []))
      else if (cmp u_2 u_1) < 0 then u_2 :: u_1 :: []	(* SPRDREC-1-4 *)
      else expr_list					(* SPRDREC-1-5 *)
      )
  | u_1 :: rest ->
      let w = simplify_product_rec rest in
      (match u_1 with
      | Mult p ->						(* SPRDREC-3-1 *)
          merge_products p w
      | _ ->
          merge_products (u_1 :: []) w				(* SPRDREC-3-2 *)
      )
  | [] ->
      (Coe (Sigs.Q.from_string_c "1")) :: []
and merge_products p q = 
  match (p, q) with
  | (_, []) -> p	(* MRPD-1 *)
  | ([], _) -> q	(* MRPD-2 *)
  | (p1 :: rest_p, q1 :: rest_q) ->
      let h = simplify_product_rec (p1 :: q1 :: []) in
      (match h with
      | [] -> merge_products rest_p rest_q	(* MRPD-3-1 *)
      | h1 :: [] -> h1 :: (merge_products rest_p rest_q)	(* MRPD-3-2 *)
      | _ ->
           if h = (p1 :: q1 :: []) then List.append (p1 :: []) (merge_products rest_p q)	(* MRPD-3-3 *)
           else if h = (q1 :: p1 :: []) then List.append (q1 :: []) (merge_products p rest_q)	(* MRPD-3-4 *)
           else failwith "Error in merge_sums"
      )
      
and simplify_product expr_list = 
  if (List.exists 
    (fun el -> (match el with
               | Coe value when Sigs.Q.is_zero value-> true	(* SPRD-2 *)
               | _ -> false)) expr_list) then Coe (Sigs.Q.from_string_c "0")
  else
     (match expr_list with
     | u_1 :: [] -> u_1		(* SPRD-3 *)
     | _ ->
         let simp_list = simplify_product_rec expr_list in 
         (match simp_list with 	(* SPRD-4 *)
         | [] -> Coe (Sigs.Q.from_string_c "1")
         | v_1 :: [] -> v_1
         | (Add sum_lis) :: (Coe rat) :: [] | (Coe rat) :: (Add sum_lis) :: [] ->
             let distributed_rat = List.map (fun x -> simplify_product [Coe rat; x]) sum_lis in
             simplify_sum distributed_rat
         | _ -> Mult simp_list
         )
      )

(* input is expr and an Mpq.t int *)
and simplify_power base n =
  if n = 0 then Coe (Sigs.Q.from_string_c "1")
  else if n = 1 then base
  else
    match base with
    | Coe rat ->	(* SINTPOW-1 *)
      let rec exp_by_squaring acc x n =
        if n < 0 then exp_by_squaring acc (Sigs.Q.divc (Sigs.Q.from_string_c "1") x) ((-1)*n)
        else if n = 0 then acc
        else if n = 1 then Sigs.Q.mulc x acc
        else
          let n_div2 = n / 2 in
          let x_sqr = Sigs.Q.mulc x x in
          if n mod 2 = 0 then
            exp_by_squaring acc x_sqr n_div2
          else
            let x_by_y = Sigs.Q.mulc x acc in
            exp_by_squaring x_by_y x_sqr n_div2
      in
      Coe (exp_by_squaring (Sigs.Q.from_string_c "1") rat n)
    | Pow (r, s) ->	(* SINTPOW-4 *)
      simplify_power r (s * n)
    | Mult expr_list ->				(*SINTPOW-5*)
      simplify_product (List.map (fun expr_list_elem -> (simplify_power expr_list_elem n)) expr_list)
    | _ ->
      Pow (base, n)

let simplify_divide num denom = 
  match denom with
  | Coe rat when Sigs.Q.is_zero rat ->
      failwith "Division by 0!"
  | _ ->
      simplify_product (num :: (simplify_power denom (-1)) :: [])

let simplify_floor x =
  match x with
  | Coe rat -> Coe (Sigs.Q.floor rat)
  | _ -> Floor x

(** Automatically simplify an expression bottom up *)
let rec simplify expr = 
  match expr with
  | Coe _ | Var _ ->
    expr
  | Pow (base, exponent) ->
    let simplified_base = simplify base in
    simplify_power simplified_base exponent
  | Mult prod_list ->
    simplify_product (List.map simplify prod_list)
  | Add sum_list ->
    simplify_sum (List.map simplify sum_list)
  | Div (num, denom) ->
    let simplified_num = simplify num in
    let simplified_denom = simplify denom in
    simplify_divide simplified_num simplified_denom
  | Floor x -> 
    let simp_x = simplify x in
    simplify_floor simp_x

let rec qify e =
  match e with
  | Coe x -> Coe (Sigs.Q.from_string_c x)
  | Var v -> Var v
  | Add l -> Add (List.map qify l)
  | Mult l -> Mult (List.map qify l)
  | Div (n, d) -> Div (qify n, qify d)
  | Pow (b, e) -> Pow (qify b, e)
  | Floor x -> Floor (qify x)

let distribute a = 
  let rec aux e =
    match e with
    | Coe _ | Var _ -> e
    | Add l -> simplify (Add (List.map aux l))
    | Mult l -> 
      let foldr acc x =
        (match acc with
        | Add add_l -> 
          (match x with
          | Add x_l -> 
            simplify (Add (List.fold_left (fun accum rel -> accum @ (List.map (fun lel -> Mult [lel; rel]) add_l)) [] x_l))
          | _ ->          
            simplify (Add (List.map (fun el -> Mult [el; x]) add_l)))
        | _ -> simplify (Mult [acc; x]))
      in
      List.fold_left foldr (Coe (Sigs.Q.from_string_c "1")) (List.map aux l)
    | Div(n, d) -> simplify (Div (aux n, aux d))
    | Pow (b, e) -> 
      let dist_b = aux b in
      if e = 0 then Coe (Sigs.Q.from_string_c "1")
      else if e = 1 then dist_b
      else
        (match dist_b with
        | Add _ -> 
          let rec replicate acc2 dupes =
            if dupes <= 0 then acc2
            else replicate (dist_b :: acc2) (dupes - 1)
          in
          aux (Mult (replicate [] e))
        | _ -> simplify (Pow(dist_b , e)))
    | Floor x -> simplify (Floor (aux x))
  in
  aux a

let from_string s = distribute (qify (ExpParse.main ExpLexer.token (Lexing.from_string s)))

let rec to_string e = 
  match e with
  | Coe x -> Sigs.Q.to_string_c x
  | Var x -> x
  | Add l -> "(" ^ (String.concat " + " (List.map to_string l)) ^ ")"
  | Mult l -> (String.concat " * " (List.map to_string l))
  | Div (n, d) -> "(" ^ (to_string n) ^ ")/(" ^ (to_string d) ^ ")"
  | Pow (b, e) -> "(" ^ (to_string b) ^ ")^" ^ (string_of_int e)
  | Floor x -> "floor(" ^ (to_string x) ^ ")"


