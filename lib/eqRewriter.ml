open Sigs.Expr


module P = Poly.PQ

module C = Poly.ConeQ

module I = Poly.IdealQ

module S = BatMap.String

module VS = BatSet.Make(String)

type fun_app = Recip of (P.poly) | Floo of (P.poly)

let pp_funapp f fun_appl = 
  Format.pp_open_box f 0;
  match fun_appl with
  | Recip p -> Format.pp_print_string f "("; P.pp f p; Format.pp_print_string f ")^-1"
  | Floo p -> Format.pp_print_string f "floor("; P.pp f p; Format.pp_print_string f ")";
  Format.pp_close_box f ()

let ppmap pp f term_map = 
  (*Format.pp_open_box f 0;*)
  Format.pp_print_string f "Variable map:";
  Format.pp_print_break f 1 4;
  Format.pp_open_vbox f 0;
  let ppvar_map fo (v, value) = 
    Format.pp_open_box fo 0;
    Format.pp_print_string fo (v ^ " ->");
    Format.pp_print_break fo 1 6;
    pp f value;
    Format.pp_close_box fo ()
  in
  Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_custom_break fo ~fits:(";", 1, "") ~breaks:("", 0, "")) ppvar_map f (S.bindings term_map);
  Format.pp_close_box f ()(*; Format.pp_close_box f ()*)


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
  res_poly, new_const, term_map, !pure_vars


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
            let () = (if (not (S.mem v_sub term_map)) && (List.mem v_sub vars_to_keep) then 
              ref_acc := S.add v_sub true !ref_acc
            else if not (S.mem v_sub term_map) then 
              ref_acc := S.add v_sub false !ref_acc
            else
              let new_acc = aux v_sub (S.find v_sub term_map) !ref_acc in
              ref_acc := new_acc) in
            S.find v_sub !ref_acc
        in
        let list_keep = List.map keep_variable (BatList.of_enum vars) in
        let keep = List.for_all (fun a -> a) list_keep in
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
      let new_map, mon_exs, new_top_order = BatEnum.fold mon_folder (curr_acc, [Coe mon_coef], old_top_order) mon_vars in
      new_map, Mult mon_exs, new_top_order
    and poly_to_expr curr_acc poly old_top_order = 
      let poly_folder (c_map, exs, o_top_order) mon = 
        let new_map, mon_exp, new_top_order = mon_to_expr c_map mon o_top_order in
        new_map, mon_exp :: exs, new_top_order
      in
      let new_map, poly_exs, new_top_order = BatEnum.fold poly_folder (curr_acc, [], old_top_order) (P.get_mons poly) in
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
    
let inst_floor_recip map =
  let folder v t (ineqs, impls) = 
    match t with
    | Floo p -> 
      let ines = [P.add p (P.negate (P.from_var v)); P.add (P.add (P.from_var v) (P.from_const_s "1")) (P.negate p)] in (* t - floor(t)>=0 floor(t) + 1 - t>=0*)
      let impl = (p, P.from_var v) in (* t >=0 => floor(t) >= 0*)
      (ines @ ineqs, impl :: impls)
    | Recip p ->
      (ineqs, (p, P.from_var v) :: impls) (* t >= 0 => 1/t >= 0*)
  in
  S.fold folder map ([], [])



(*let effective_deg_ord_as_list deg_map keep_map top_order ps = 
  let vars = S.keys keep_map in
  let (keep_vars, discard_vars) = BatEnum.partition (fun v -> S.find v keep_map) vars in
  let cmp_var x y =
    match (List.find_opt (fun (_, v) -> v = x) top_order, List.find_opt (fun (_, v) -> v = y) top_order) with
    | None, None -> (-1) *(compare x y)
    | Some (_, _), None -> 1
    | None, Some (_, _) -> (-1)
    | Some (x_ind, _), Some (y_ind, _) ->
      compare x_ind y_ind
  in
  let var_ord = (List.sort cmp_var (BatList.of_enum keep_vars)) @ (List.sort cmp_var (BatList.of_enum discard_vars)) in
  let folder (svar_ord, svar_to_pvar_e, polys) pvar = 
    let pedeg = match S.find_opt pvar deg_map with | None -> 1 | Some e -> e in
    let svar = new_var () in
    let svar_edeg = P.from_var_pow svar pedeg in
    let sub_ps = List.map (P.substitute (pvar, svar_edeg)) polys in
    svar :: svar_ord, S.add svar (pvar, pedeg) svar_to_pvar_e, sub_ps
  in
  let rord, svar_to_pvar, subps = List.fold_left folder ([], S.empty, ps) var_ord in
  (var_ord, List.rev rord, svar_to_pvar, subps)*)

    

(*let effective_deg_ord deg_map keep_map pure_vars top_order a b =
  let a_vars = P.get_vars_m a in
  let b_vars = P.get_vars_m b in
  let (avd, bvd) = (BatEnum.map (fun v -> v, P.get_degree v a) a_vars, BatEnum.map (fun v -> v, P.get_degree v b) b_vars) in
  let folder (rem_deg, keep_deg) (v, d) = 
    if S.find v keep_map then 
      if S.mem v deg_map then (rem_deg, keep_deg + d * (S.find v deg_map))
      else (rem_deg, keep_deg + d)
    else
      if S.mem v deg_map then (rem_deg + d * (S.find v deg_map), keep_deg)
      else (rem_deg + d, keep_deg)
  in
  let (a_deg, b_deg) = (BatEnum.fold folder (0, 0) avd, BatEnum.fold folder (0, 0) bvd) in
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
      let (a_s, b_s) = (List.rev (List.sort cmp_var (BatList.of_enum avd)), List.rev (List.sort cmp_var (BatList.of_enum bvd))) in
      well_formed_lex a_s b_s
    else compare (snd a_deg) (snd b_deg)
  else compare (fst a_deg) (fst b_deg)*)

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
      ) (BatList.of_enum mon_vars)))
  in
  let poly_to_expr poly = Add (List.map mon_to_expr (BatList.of_enum (P.get_mons poly))) in
  List.map (fun p -> Expr.simplify (poly_to_expr p)) polys, top_order

let update_map ideal term_map t_p eqs ineqs = 
  let reduce v term (acc_map, const_sub) =
    match term with
    | Floo p -> 
      let p_red = I.reduce p ideal in
      if P.is_const p_red then
        let const = fst (List.hd (BatList.of_enum (P.get_mons p_red))) in
        (acc_map, (v, P.from_const (Sigs.Q.floor const)) :: const_sub)
      else
        S.add v (Floo p_red) acc_map, const_sub
    | Recip p ->
      let p_red = I.reduce p ideal in
      if P.is_const p_red then
        let const = fst (List.hd (BatList.of_enum (P.get_mons p_red))) in
        (acc_map, (v, P.from_const (Sigs.Q.divc (Sigs.Q.from_string_c "1") const)) :: const_sub)
      else
        S.add v (Recip p_red) acc_map, const_sub
  in
  let reduced_map, const_subs = S.fold reduce term_map (S.empty, []) in
  let sub_consts term = 
    match term with
    | Floo p -> 
      Floo (List.fold_left (fun p2 s -> P.substitute s p2) p const_subs)
    | Recip p -> 
      Recip (List.fold_left (fun p2 s -> P.substitute s p2) p const_subs)
  in
  let sub_polys = List.map (fun p -> List.fold_left (fun p2 s -> P.substitute s p2) p const_subs) in
  let eqs = sub_polys eqs in
  let ineqs = sub_polys ineqs in
  let reduced_map = S.map sub_consts reduced_map in
  let bindings = fst (List.split (S.bindings reduced_map)) in
  let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
  let pairs = get_pairs bindings in
  let rec aux rm_pairs (old_eqs, old_ineqs, old_tp, old_map) =
    match rm_pairs with
    | [] -> (old_eqs, old_ineqs, old_tp, old_map)
    | (x_i, x_j) :: l ->
      match (S.find_opt x_i old_map, S.find_opt x_j old_map) with
      | Some (Recip t_i), Some (Recip t_j) | Some (Floo t_i), Some (Floo t_j) -> 
        let remove_var_sub rem sub equa ine t_prime map =
          let rem_map = S.remove rem map in
          let sub_poly = P.from_var sub in
          let new_map = S.map (sub_fun_app_var rem sub_poly) rem_map in
          let new_eqs = List.map (P.substitute (rem, sub_poly)) equa in
          let new_ineqs = List.map (P.substitute (rem, sub_poly)) ine in
          let new_t_prime = P.substitute (rem, sub_poly) t_prime in
          (new_eqs, new_ineqs, new_t_prime, new_map)
        in
        if (P.compare t_i t_j) = 0 then 
          let (new_eqs, new_ineqs, new_t, new_map) = remove_var_sub x_i x_j old_eqs old_ineqs old_tp old_map in
          aux l (new_eqs, new_ineqs, new_t, new_map) (*Potentially cheaper equality check*)
        else
          let subtract_poly = P.add t_i (P.negate t_j) in
          if I.mem subtract_poly ideal then 
            let (new_eqs, new_ineqs, new_t, new_map) = remove_var_sub x_i x_j old_eqs old_ineqs old_tp old_map in
            aux l (new_eqs, new_ineqs, new_t, new_map)
          else aux l (old_eqs, old_ineqs, old_tp, old_map)
      | _ -> aux l (old_eqs, old_ineqs, old_tp, old_map)
  in
  let red_t = I.reduce t_p ideal in
  aux pairs (eqs, ineqs, red_t, reduced_map)

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
          if P.equal a_p b_p then true
          else false
        | _ -> false
    in
    List.fold_left folder true a_keys
  
(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite ?sat:(sat=3) (eqs : Expr.qexpr list) (ineqs : Expr.qexpr list) vars_to_keep (t : Expr.qexpr) = 
  let fold_eqs (old_eqs, old_tmap, old_pure_vars) term =
    let (eq, derived_eqs, tmap, pure_vars) = purify term in
    (eq :: old_eqs @ derived_eqs, S.union (fun _ _ _ -> failwith "duplicate in term map") old_tmap tmap, VS.union old_pure_vars pure_vars)
  in
  let (eqs, term_map, pure_vars) = List.fold_left fold_eqs ([], S.empty, VS.empty) eqs in
  let fold_ineq (old_ineq, equat, old_tmap, old_pure_vars) term = 
    let (ineq, derived_eqs, tmap, pure_vars) = purify term in
    (ineq :: old_ineq, equat @ derived_eqs, S.union (fun _ _ _ -> failwith "duplicate in term map") old_tmap tmap, VS.union old_pure_vars pure_vars)
  in
  let (ineqs, equat, term_map, pure_vars) = List.fold_left fold_ineq ([], eqs, term_map, pure_vars) ineqs in
  let t_p, tp_eq, t_map, t_pure_vars = purify t in
  let eqs = tp_eq @ equat in
  let term_map, _ = S.union (fun _ _ _ -> failwith "duplicate in term map") t_map term_map, VS.union t_pure_vars pure_vars in
  let keep_folder acc v =
    if S.mem v acc then acc
    else if List.mem v vars_to_keep then S.add v true acc
    else S.add v false acc
  in

  let calc_ideal t_map all_vars eqs = 
    let deg_map, top_order = calc_deg_map t_map in
    let keep_map = BatEnum.fold keep_folder (calc_keep_vars t_map vars_to_keep) all_vars in
    I.make_ideal_f deg_map keep_map top_order eqs
  in

  let iteration t_map tp ideal ineq =
    Log.log ~level:`debug (ppmap pp_funapp) (Some t_map);
    Log.log_s ~level:`debug "Curr t: ";
    Log.log ~level:`debug P.pp (Some tp);
    let (new_eqs, new_ineqs, new_t, new_map) = update_map ideal t_map tp (I.get_generators ideal) ineq in
    Log.log_line_s ~level:`trace "Next ideal";
    let new_ideal = calc_ideal t_map (BatEnum.concat (BatEnum.map P.get_vars (BatList.enum (tp::new_eqs @ new_ineqs)))) new_eqs in
    Log.log ~level:`debug I.ppi (Some new_ideal);
    new_map, new_t, new_ideal, new_ineqs
  in
  let rec loop old_map t_map tp ideal inequalities =
    if P.is_const tp then 
      let unpure_t, _ = unpurify [tp] t_map in
      List.hd unpure_t
    else if equal_t_map old_map t_map then 
      let (inequ, impls) = inst_floor_recip t_map in
      let cone = C.make_cone_i ~sat:sat ~ineqs:(inequalities @ inequ) ~impls:impls ideal in
      Log.log ~level:`debug C.ppc (Some cone);
      let red_tp = C.reduce tp cone in
      let unpure_t, _ = unpurify [red_tp] t_map in
      List.hd (unpure_t)
    else
      let (new_map, new_t, new_ideal, new_ineqs) = iteration t_map tp ideal inequalities in
      loop t_map new_map new_t new_ideal new_ineqs
  in
  Log.log_line_s ~level:`trace "Initial ideal";
  let ideal = calc_ideal term_map (BatEnum.concat (BatEnum.map P.get_vars (BatList.enum (t_p::eqs @ ineqs)))) eqs in
  Log.log ~level:`debug I.ppi (Some ideal);
  let (new_map, new_t, new_ideal, new_ineqs) = iteration term_map t_p ideal ineqs in
  loop term_map new_map new_t new_ideal new_ineqs

  