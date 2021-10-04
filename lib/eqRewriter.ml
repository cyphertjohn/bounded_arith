open Sigs.Expr

module P = Poly.Make(Sigs.Q)

module C = Poly.Cone(Sigs.Q)

module S = Map.Make(String)

module VS = Set.Make(String)

type fun_app = Recip of (P.poly) | Floo of (P.poly)


let log_keep_map keep_map =
  let mapping_to_string v keep acc = (v ^ " -> " ^ (string_of_bool keep)) :: acc in
  let map_string = String.concat "\n" (S.fold mapping_to_string keep_map []) in
  Log.log_line ~level:`trace "Keep Map";
  Log.log_line ~level:`trace map_string;
  Log.log_line ~level:`trace ""

let log_term_map term_map = 
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
  in
  Log.log_line ~level:`debug "Curr Map";
  Log.log_line ~level:`debug (var_map_to_string term_map);
  Log.log_line ~level:`debug ""

let log_t tp = 
  Log.log_line ~level:`debug ("Curr t : " ^ (P.to_string tp));
  Log.log_line ~level:`debug ""

let log_polys ps = 
  Log.log_line ~level:`debug ("Curr Polys");
  Log.log_line ~level:`debug (String.concat "\n" (List.map P.to_string ps));
  Log.log_line ~level:`debug ""

let log_top_order top = 
  Log.log_line ~level:`trace ("Top order");
  Log.log_line ~level:`trace ("[ " ^ (String.concat ";" (List.map (fun (i, v) -> "(" ^ (string_of_int i) ^ ", " ^ v ^ ")") top)) ^ "]\n");
  Log.log_line ~level:`trace ("")

let sub_fun_app_var var_to_replace poly_to_replace_with term = 
  match term with
  | Recip p -> Recip (P.substitute (var_to_replace , poly_to_replace_with) p)
  | Floo p -> Floo (P.substitute (var_to_replace , poly_to_replace_with) p)

let curr = ref 0

let new_var () = 
  let x = "x_"^ (string_of_int !curr) in
  curr := !curr + 1;
  x

let purify ex =
  let map_union _ _ _ = failwith "Duplicated fresh variable" in
  let pure_vars = ref VS.empty in
  let rec aux e = 
    match e with
    | Coe x -> (P.from_const x, ([], S.empty))
    | Var x -> (P.from_var x, ([], S.empty))
    | Add l -> 
      let pure_l, new_polys_map = List.split (List.map aux l) in
      let new_polys, new_map = List.split new_polys_map in
      (List.fold_left P.add (List.hd pure_l) (List.tl pure_l), (List.concat new_polys, List.fold_left (S.union map_union) S.empty new_map))
    | Mult l -> 
      let pure_l, new_polys_map = List.split (List.map aux l) in
      let new_polys, new_map = List.split new_polys_map in
      (List.fold_left P.mul (List.hd pure_l) (List.tl pure_l), (List.concat new_polys, List.fold_left (S.union map_union) S.empty new_map))
    | Div (n, d) -> 
      let (pure_n, (num_polys, num_map)) = aux n in
      let (pure_d, (den_polys, den_map)) = aux d in
      let new_variable = new_var () in
      pure_vars := VS.add new_variable !pure_vars;
      let new_var_poly = P.from_var new_variable in
      let new_poly = P.add (P.mul new_var_poly pure_d) (P.from_const_s "-1") in
      (P.mul pure_n new_var_poly, (new_poly :: (num_polys @ den_polys), S.add new_variable (Recip pure_d) (S.union map_union num_map den_map)))
    | Floor x -> 
      let (pure_x, (x_polys, x_map)) = aux x in
      let new_variable = new_var () in
      pure_vars := VS.add new_variable !pure_vars;
      (P.from_var new_variable, (x_polys, S.add new_variable (Floo pure_x) x_map))
    | Pow (base, exp) ->
      let (pure_base, (base_polys, base_map)) = aux base in
      if exp >= 0 then (P.exp_poly pure_base exp, (base_polys, base_map))
      else
        let neg_exp = (-1) * exp in
        let new_variable = new_var () in
        pure_vars := VS.add new_variable !pure_vars;
        let new_var_poly = P.from_var new_variable in
        let mul = P.mul new_var_poly pure_base in
        let new_poly = P.add mul (P.from_const_s "-1") in
        let res = (P.exp_poly new_var_poly neg_exp, (new_poly :: base_polys, S.add new_variable (Recip pure_base) base_map)) in
        res
    in
  let res_poly, (new_const, term_map) = aux ex in
  res_poly :: new_const, term_map, !pure_vars


(*let term_vars map = 
  let folder v term vars =
    match term with
    | Recip p | Floo p -> v :: (get_vars p) @ vars
  in
  S.fold folder map []*)

let calc_keep_vars term_map vars_to_keep =
  let rec aux v term acc = 
    if S.mem v acc then acc
    else
      match term with
      | Recip p | Floo p ->
        let vars = P.get_vars p in
        let ref_acc = ref acc in
        let keep_variable v_sub =
          if S.mem v_sub !ref_acc then S.find v_sub !ref_acc
          else 
            let () = (if not (S.mem v_sub term_map) && (List.mem v_sub vars_to_keep) then 
              ref_acc := S.add v_sub true !ref_acc
            else if not (S.mem v_sub term_map) then 
              ref_acc := S.add v_sub false !ref_acc
            else
              let new_acc = aux v_sub (S.find v_sub term_map) !ref_acc in
              ref_acc := new_acc) in
            S.find v_sub !ref_acc
        in
        let keep = List.for_all keep_variable vars in
        S.add v keep !ref_acc
  in
  let res = S.fold aux term_map S.empty in
  res

let unpurify_map term_map =
  let folder v _ (acc, top_order)= 
    let rec var_to_expr curr_acc var old_top_order= 
      if not (S.mem var term_map) then curr_acc, Var var, old_top_order
      else 
        if S.mem var curr_acc then curr_acc, S.find var curr_acc, old_top_order
        else
          let term = S.find var term_map in
          let new_acc, term_ex, new_top_order = fun_app_to_expr curr_acc term old_top_order in
          S.add var term_ex new_acc, term_ex, var :: new_top_order
    and mon_to_expr curr_acc mon old_top_order= 
      let mon_coef = fst mon in
      let mon_vars = P.get_vars_m (snd mon) in
      let mon_folder (c_map, exs, o_top_order) var = 
        let new_map, var_exp, new_top_order = var_to_expr c_map var o_top_order in
        new_map, var_exp :: exs, new_top_order
      in
      let new_map, mon_exs, new_top_order = List.fold_left mon_folder (curr_acc, [Coe mon_coef], old_top_order) mon_vars in
      new_map, Mult mon_exs, new_top_order
    and poly_to_expr curr_acc poly old_top_order = 
      let poly_folder (c_map, exs, o_top_order) mon = 
        let new_map, mon_exp, new_top_order = mon_to_expr c_map mon o_top_order in
        new_map, mon_exp :: exs, new_top_order
      in
      let new_map, poly_exs, new_top_order = List.fold_left poly_folder (curr_acc, [], old_top_order) (P.get_mons poly) in
      new_map, Add poly_exs, new_top_order
    and fun_app_to_expr curr_acc fun_ap old_top_order = 
      match fun_ap with
      | Floo p -> 
        let new_acc, p_expr, new_top_order = poly_to_expr curr_acc p old_top_order in
        new_acc, Floor p_expr, new_top_order
      | Recip p -> 
        let new_acc, p_expr, new_top_order = poly_to_expr curr_acc p old_top_order in
        new_acc, Pow (p_expr, -1), new_top_order
    in
    let new_acc, _, new_top = var_to_expr acc v top_order in
    new_acc, new_top
  in
  let unpure_map, top_order = S.fold folder term_map (S.empty, []) in
  unpure_map, List.mapi (fun i v -> i, v) (List.rev top_order)

let calc_deg_map term_map =
  let unpure_map, top_order = unpurify_map term_map in
  let rec effective_degree expr = 
    match expr with
    | Var _ -> 1
    | Coe _ -> 0
    | Div (n, d) -> (effective_degree n) + (effective_degree d)
    | Add l -> List.fold_left max (-1) (List.map effective_degree l)
    | Mult l -> List.fold_left (+) 0 (List.map effective_degree l)
    | Pow(b, e) -> 
      if e < 0 then (effective_degree b) * e * (-1)
      else (effective_degree b) * e
    | Floor e -> effective_degree e
  in
  S.map effective_degree unpure_map, top_order
    

let effective_deg_ord deg_map keep_map pure_vars top_order a b =
  let a_vars = P.get_vars_m a in
  let b_vars = P.get_vars_m b in
  let (avd, bvd) = (List.map (fun v -> v, P.get_degree v a) a_vars, List.map (fun v -> v, P.get_degree v b) b_vars) in
  let folder (rem_deg, keep_deg) (v, d) = 
    if S.find v keep_map then 
      if S.mem v deg_map then (rem_deg, keep_deg + d * (S.find v deg_map))
      else (rem_deg, keep_deg + d)
    else
      if S.mem v deg_map then (rem_deg + d * (S.find v deg_map), keep_deg)
      else (rem_deg + d, keep_deg)
  in
  let (a_deg, b_deg) = (List.fold_left folder (0, 0) avd, List.fold_left folder (0, 0) bvd) in
  if (fst a_deg = fst b_deg) then 
    if (snd a_deg = snd b_deg) then
      let cmp_var (x, xe) (y, ye) = 
        if x = y then compare xe ye
        else if VS.mem x pure_vars then
          if VS.mem y pure_vars then
            let x_ind = fst (List.find (fun (_, v) -> v = x) top_order) in
            let y_ind = fst (List.find (fun (_, v) -> v = y) top_order) in
            compare x_ind y_ind
          else 1
        else if VS.mem y pure_vars then -1
        else compare x y
      in
      let rec well_formed_lex al bl =
        match al, bl with
        | [], [] -> 0
        | _ :: _ , [] -> -1
        | [], _ :: _ -> 1
        | x :: xs, y :: ys ->
          let cmp_res = cmp_var x y in
          if cmp_res = 0 then well_formed_lex xs ys
          else cmp_res
      in
      let (a_s, b_s) = (List.rev (List.sort cmp_var avd), List.rev (List.sort cmp_var bvd)) in
      well_formed_lex a_s b_s
    else compare (snd a_deg) (snd b_deg)
  else compare (fst a_deg) (fst b_deg)

let unpurify polys term_map =
  let unpure_map, top_order = unpurify_map term_map in
  let mon_to_expr (c, mon) = 
    let mon_vars = P.get_vars_m mon in
    Mult ((Coe c) :: (List.map 
      (fun mv -> 
        let deg = P.get_degree mv mon in
        if S.mem mv unpure_map then 
          Pow (S.find mv unpure_map, deg)
        else
          if deg = 1 then Var mv
          else Pow(Var mv, deg)
      ) mon_vars))
  in
  let poly_to_expr poly = Add (List.map mon_to_expr (P.get_mons poly)) in
  List.map (fun p -> Expr.simplify (poly_to_expr p)) polys, top_order

let update_map id term_map polys t_p = 
  let reduce v term (cone, acc_map) =
    match term with
    | Floo p -> 
      let red, new_cone = C.reduce_eq p cone in
      new_cone, S.add v (Floo red) acc_map
    | Recip p ->
      let red, new_cone = C.reduce_eq p cone in
      new_cone, S.add v (Recip red) acc_map
  in
  let cone, reduced_map = S.fold reduce term_map (id, S.empty) in
  let bindings = fst (List.split (S.bindings reduced_map)) in
  let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
  let pairs = get_pairs bindings in
  let rec aux rm_pairs (old_polys, old_tp, old_map, old_cone) =
    match rm_pairs with
    | [] -> (old_polys, old_tp, old_map)
    | (x_i, x_j) :: l ->
      match (S.find_opt x_i old_map, S.find_opt x_j old_map) with
      | Some (Recip t_i), Some (Recip t_j) | Some (Floo t_i), Some (Floo t_j) -> 
        let remove_var_sub rem sub polys t_prime map =
          let rem_map = S.remove rem map in
          let sub_poly = P.from_var sub in
          let new_map = S.map (sub_fun_app_var rem sub_poly) rem_map in
          let new_polys = List.map (P.substitute (rem, sub_poly)) polys in
          let new_t_prime = P.substitute (rem, sub_poly) t_prime in
          (new_polys, new_t_prime, new_map)
        in
        if (P.compare t_i t_j) = 0 then 
          let (new_p, new_t, new_map) = remove_var_sub x_i x_j old_polys old_tp old_map in
          aux l (new_p, new_t, new_map, old_cone) (*Potentially cheaper equality check*)
        else
          let subtract_poly = P.add t_i (P.negate t_j) in
          let sub_rem, new_cone = C.reduce_eq subtract_poly old_cone in
          if P.is_zero sub_rem then 
            let (new_p, new_t, new_map) = remove_var_sub x_i x_j old_polys old_tp old_map in
            aux l (new_p, new_t, new_map, new_cone) (*Potentially cheaper equality check*)
          else aux l (old_polys, old_tp, old_map, new_cone)
      | _ -> aux l (old_polys, old_tp, old_map, old_cone)
  in
  let red_t, new_cone = C.reduce t_p cone in
  aux pairs (polys, red_t, reduced_map, new_cone)

let equal_t_map a b = 
  let a_keys = fst (List.split (S.bindings a)) in
  let b_keys = fst (List.split (S.bindings b)) in
  if (List.sort compare a_keys) <> (List.sort compare b_keys) then
    false
  else
    let folder prev_eq v =
      if not prev_eq then prev_eq
      else 
        let a_term = S.find v a in
        let b_term = S.find v b in
        match (a_term, b_term) with
        | Recip a_p, Recip b_p | Floo a_p, Floo b_p ->
          if P.compare a_p b_p = 0 then true
          else false
        | _ -> false
    in
    List.fold_left folder true a_keys
  
(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite terms vars_to_keep t = 
  let foldr (old_pol, old_tmap, old_pure_vars) term =
    let (pols, tmap, pure_vars) = purify term in
    (old_pol @ pols, S.union (fun _ _ _ -> failwith "duplicate in term map") old_tmap tmap, VS.union old_pure_vars pure_vars)
  in
  let (t_and_polys, term_map, pure_vars) = List.fold_left foldr ([], S.empty, VS.empty) (t :: terms) in
  let (t_poly, polys) = match t_and_polys with
    | t_p :: rest -> (t_p, rest)
    | [] -> failwith "t has become empty"
  in
  let keep_folder acc v =
    if S.mem v acc then acc
    else if List.mem v vars_to_keep then S.add v true acc
    else S.add v false acc
  in
  let iteration t_map tp ps =
    log_term_map t_map;
    log_t tp;
    log_polys ps;
    let deg_map, top_order = calc_deg_map t_map in
    log_top_order top_order;
    (*let tvars = term_vars term_map in*)
    let keep_map = List.fold_left keep_folder (calc_keep_vars t_map vars_to_keep) (List.concat (List.map P.get_vars (tp::ps))) in
    log_keep_map keep_map;
    (*P.set_ord (fun a b -> Log.log_time_cum "Monomial order" ((effective_deg_ord deg_map keep_map) a) b);*)
    let new_cone = C.add_eqs ps (C.initialize (effective_deg_ord deg_map keep_map pure_vars top_order)) in
    update_map new_cone t_map ps tp 
  in
  let rec loop old_map t_map tp ps =
    if equal_t_map old_map t_map then 
      let unpure_t, _ = unpurify [tp] t_map in
      List.hd (unpure_t)
    else
      let (new_polys, new_t, new_map) = iteration t_map tp ps in
      loop t_map new_map new_t new_polys
  in
  loop S.empty term_map t_poly polys

  