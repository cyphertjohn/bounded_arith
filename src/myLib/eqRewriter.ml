open Sigs.Expr
open Sigs.Polynomial
open Poly

module S = Map.Make(String)

type 'a fun_app = Recip of ('a polynomial) | Floo of ('a polynomial)

let curr = ref 0
let new_var () = 
  let x = "x_"^ (string_of_int !curr) in
  curr := !curr + 1;
  x

let purify ex =
  let map_union _ _ _ = failwith "Duplicated fresh variable" in
  let rec aux e = 
    match e with
    | Coe x -> (Sum ([(Coef x, Prod [])]), ([], S.empty))
    | Var x -> (Sum ([(Coef (Sigs.Q.from_string_c "1"), Prod[Exp (x, 1)])]), ([], S.empty))
    | Add l -> 
      let pure_l, new_polys_map = List.split (List.map aux l) in
      let new_polys, new_map = List.split new_polys_map in
      (List.fold_left P.add (List.hd pure_l) (List.tl pure_l), (List.concat new_polys, List.fold_left (S.union map_union) S.empty new_map))
    | Mult l -> 
      let pure_l, new_polys_map = List.split (List.map aux l) in
      let new_polys, new_map = List.split new_polys_map in
      (List.fold_left P.mult (List.hd pure_l) (List.tl pure_l), (List.concat new_polys, List.fold_left (S.union map_union) S.empty new_map))
    | Div (n, d) -> 
      let (pure_n, (num_polys, num_map)) = aux n in
      let (pure_d, (den_polys, den_map)) = aux d in
      let new_variable = new_var () in
      let new_var_poly = Sum ([(Coef (Sigs.Q.from_string_c "1"), Prod[Exp (new_variable, 1)])]) in
      let new_poly = P.add (P.mult new_var_poly pure_d) P.minus_1 in
      (P.mult pure_n new_var_poly, (new_poly :: (num_polys @ den_polys), S.add new_variable (Recip pure_d) (S.union map_union num_map den_map)))
    | Floor x -> 
      let (pure_x, (x_polys, x_map)) = aux x in
      let new_variable = new_var () in
      (Sum ([(Coef (Sigs.Q.from_string_c "1"), Prod[Exp (new_variable, 1)])]), (x_polys, S.add new_variable (Floo pure_x) x_map))
    | Pow (base, exp) ->
      let (pure_base, (base_polys, base_map)) = aux base in
      if exp >= 0 then (P.exp_poly pure_base exp, (base_polys, base_map))
      else
        let neg_exp = (-1) * exp in
        let new_variable = new_var () in
        let new_var_poly = Sum ([(Coef (Sigs.Q.from_string_c "1"), Prod[Exp (new_variable, 1)])]) in
        let mul = P.mult new_var_poly pure_base in
        let new_poly = P.add mul P.minus_1 in
        let res = (P.exp_poly new_var_poly neg_exp, (new_poly :: base_polys, S.add new_variable (Recip pure_base) base_map)) in
        res
    in
  let res_poly, (new_const, term_map) = aux ex in
  res_poly :: new_const, term_map

let var_map_to_string var_map = 
  let mapping_to_string v fun_map acc = 
    let map_str =
      match fun_map with
      | Recip poly -> v ^ " -> " ^ "(" ^ (P.to_string poly) ^ ")^-1"
      | Floo poly -> v ^ " -> " ^ "floor(" ^ (P.to_string poly) ^ ")"
    in
    map_str :: acc
  in
  String.concat "\n" (S.fold mapping_to_string var_map [])


let get_vars (Sum poly) = 
  let get_vars_m (_, Prod mon) = 
    List.map (fun (Exp (v, _)) -> v) mon
  in
  List.concat (List.map get_vars_m poly)

let term_vars map = 
  let folder v term vars =
    match term with
    | Recip p | Floo p -> v :: (get_vars p) @ vars
  in
  S.fold folder map []

let calc_keep_vars term_map vars_to_keep =
  let rec aux v term acc = 
    if S.mem v acc then acc
    else
      match term with
      | Recip p | Floo p ->
        let vars = get_vars p in
        let ref_acc = ref acc in
        let keep_variable v =
          if S.mem v acc then S.find v !ref_acc
          else if not (S.mem v term_map) && (List.mem v vars_to_keep) then true
          else if not (S.mem v term_map) then false
          else
            let new_acc = aux v (S.find v term_map) !ref_acc in
            ref_acc := new_acc;
            S.find v !ref_acc
        in
        let keep = List.for_all keep_variable vars in
        S.add v keep !ref_acc
  in
  S.fold aux term_map S.empty


let calc_deg_map term_map =
  let rec deg_mon (_, Prod m) =
    let deg_var_exp (Exp (v, d)) = 
      d * (deg_var v)
    in
    List.fold_left (+) 0 (List.map deg_var_exp m)
  and deg_var v =  
    match (S.find_opt v term_map) with
    | None -> 1
    | Some (Recip p) | Some (Floo p) -> deg_poly p
  and deg_poly (Sum p) =
    List.fold_left (max) (-1) (List.map deg_mon p)
  in
  let dummy v _ = deg_var v in
  S.mapi dummy term_map
    

let effective_deg_ord deg_map keep_map (Prod a) (Prod b) =
  let folder (rem_deg, keep_deg) (Exp (v, d)) = 
    if S.find v keep_map then 
      if S.mem v deg_map then (rem_deg, keep_deg + d * (S.find v deg_map))
      else (rem_deg, keep_deg + d)
    else
      if S.mem v deg_map then (rem_deg + d * (S.find v deg_map), keep_deg)
      else (rem_deg + d, keep_deg)
  in
  let (a_deg, b_deg) = (List.fold_left folder (0, 0) a, List.fold_left folder (0, 0) b) in
  if (fst a_deg = fst b_deg) then 
    if (snd a_deg = snd b_deg) then Mon.lex_ord (Prod a) (Prod b)
    else compare (snd a_deg) (snd b_deg)
  else compare (fst a_deg) (fst b_deg)

let unpurify polys term_map =
  let rec make_subsituter var term acc =
    let (_, handled) = acc var in
    if handled then acc
    else
      let monomial_sub (cont, l) (Coef x, Prod m) =
        let sub_var_pow (cont1, l1) (Exp(v, e)) =
          let (v_sub, v_handled) = cont1 v in
          if v_handled then (cont1, (Pow (v_sub, e)) :: l1)
          else
            if not (S.mem v term_map) then
              let new_fun = function variable -> if v = variable then (Var v, handled) else cont1 variable in
              (new_fun, (Pow (Var v, e)) :: l1)
            else
              let new_sub = make_subsituter v (S.find v term_map) cont1 in
              let (sub_expr, _) = new_sub v in
              (new_sub, (Pow (sub_expr, e)) :: l1)
        in
        let (new_cont, monomial_subs) = List.fold_left sub_var_pow (cont, []) m in
        (new_cont, (Mult ((Coe x) :: monomial_subs)) :: l) 
      in
      match term with
      | Floo (Sum p) ->
        let (new_cont, p_exprs) = List.fold_left monomial_sub (acc, []) p in
        let new_term = Floor (Add p_exprs) in
        (function variable -> if variable = var then new_term, true else new_cont variable)
      | Recip (Sum p) ->
        let (new_cont, p_exprs) = List.fold_left monomial_sub (acc, []) p in
        let new_term = Pow ((Add p_exprs), -1) in
        (function variable -> if variable = var then new_term, true else new_cont variable)
    in
  let substituter = S.fold make_subsituter term_map (function _ -> (Coe (Mon.from_string_c "0"), false)) in
  let sub_poly (Sum p) = 
    let sub_var_pow (Exp (v, e)) =
      Pow(fst (substituter v), e)
    in
    let sub_mon (Coef c, Prod m) = 
      Mult (Coe c :: List.map sub_var_pow m)
    in
    Expr.simplify (Add (List.map sub_mon p))
  in
  List.map sub_poly polys

let update_map g_basis term_map = 
  let reduce term =
    match term with
    | Floo p -> 
      let red = snd (P.division g_basis p) in
      Floo red
    | Recip p ->
      let red = snd (P.division g_basis p) in
      Recip red
  in
  let reduced_map = S.map reduce term_map in
  reduced_map 



let rewrite terms vars_to_keep = 
  P.set_ord (Mon.lex_ord);
  let foldr (old_pol, old_tmap) term =
    let (pols, tmap) = purify term in
    (old_pol @ pols, S.union (fun _ _ _ -> failwith "duplicate in term map") old_tmap tmap)
  in
  let polys, term_map = List.fold_left foldr ([], S.empty) terms in
  let deg_map = calc_deg_map term_map in
  let folder acc v =
    if S.mem v acc then acc
    else if List.mem v vars_to_keep then S.add v true acc
    else S.add v false acc
  in
  let tvars = term_vars term_map in
  let keep_map = List.fold_left folder (calc_keep_vars term_map vars_to_keep) ((List.concat (List.map get_vars polys)) @ tvars) in
  P.set_ord (effective_deg_ord deg_map keep_map);
  let g_basis = P.improved_buchberger polys in
  g_basis

  