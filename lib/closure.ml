module Make(P : Poly.Polynomial) = struct
  module I = Ideal.Make(P)
  module S = P.V.M

  include P
  
  open Sigs.Expr

  type closure = {
    ideal: I.ideal;
    map: (string * poly) S.map;
    deg_map: int S.map;
    top_order: V.v list;
    eliminated_vars: poly S.map;
    (*vars_to_keep: V.v list;
    vars_to_remove: V.v list;*)
    constants: bool S.map;
    non_dummy_vars : P.V.v list;
    vars_to_keep : bool S.map
  }

  let get_num_eqs c = 
    let ideal_size = List.length (I.get_generators c.ideal) in
    ideal_size + (S.cardinal c.eliminated_vars)

  let create_order tbl ord a b = 
    try BatHashtbl.find tbl (a, b)
    with Not_found ->
      let res = ord a b in
      BatHashtbl.add tbl (a, b) res;
      BatHashtbl.add tbl (b, a) (-1*res);
      res
    

  let ppmap pp f term_map = 
    Format.pp_open_vbox f 0;
    let ppvar_map fo (v, value) = 
      Format.pp_open_box fo 0;
      Format.pp_print_string fo ((V.to_string v) ^ " ->");
      Format.pp_print_break fo 1 6;
      pp f value;
      Format.pp_close_box fo ()
    in
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_custom_break fo ~fits:(";", 1, "") ~breaks:("", 0, "")) ppvar_map f (S.bindings term_map);
    Format.pp_close_box f ()(*; Format.pp_close_box f ()*)

  let pp_fun ord f (fu, p) = 
    if fu = "recip" then (Format.pp_print_string f "("; pp ~ord:ord f p; Format.pp_print_string f ")^-1")
    else (Format.pp_print_string f (fu ^ "("); pp ~ord:ord f p; Format.pp_print_string f ")")

  let pp_cm ord f m = ppmap (pp_fun ord) f m

  let pp_c f c = 
    Format.pp_open_hvbox f 0;
    Format.pp_print_string f "Function map: ";
    Format.pp_print_break f 1 4;
    pp_cm (I.get_ord c.ideal) f c.map; Format.pp_print_space f ();

    Format.pp_print_string f "Eliminated vars: ";
    Format.pp_print_break f 1 4;
    ppmap (pp ~ord:(I.get_ord c.ideal)) f c.eliminated_vars; Format.pp_print_space f ();

    Format.pp_print_string f "Deg Map: ";
    Format.pp_print_break f 1 4;
    ppmap (Format.pp_print_int) f c.deg_map; Format.pp_print_space f ();

    Format.pp_print_string f "Keep Map: ";
    Format.pp_print_break f 1 4;
    ppmap (Format.pp_print_bool) f c.vars_to_keep; Format.pp_print_space f ();

    Format.pp_print_string f "Const Map: ";
    Format.pp_print_break f 1 4;
    ppmap (Format.pp_print_bool) f c.constants; Format.pp_print_space f ();

    Format.pp_print_string f "Top order: ";
    Format.pp_print_break f 1 4; Format.pp_open_box f 0;
    Format.pp_print_string f "["; 
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) Format.pp_print_string f (List.map V.to_string c.top_order);
    Format.pp_print_string f "]"; Format.pp_close_box f (); Format.pp_print_space f ();

    Format.pp_print_string f "Given Variables: ";
    Format.pp_print_break f 1 4; Format.pp_open_box f 0;
    Format.pp_print_string f "["; 
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) Format.pp_print_string f (List.map V.to_string c.non_dummy_vars);
    Format.pp_print_string f "]"; Format.pp_close_box f (); Format.pp_print_space f ();

    I.ppi f c.ideal; Format.pp_print_space f (); Format.pp_close_box f ()
  

  let purify ex c =
    let rec aux (top_order, p_map, d_map, vars) e = 
      match e with
      | Coe x -> (from_const x, 0, (top_order, p_map, d_map, vars))
      | Var x -> 
        let xvar = V.of_string x in
        if List.mem xvar vars then (from_var xvar, 1, (top_order, p_map, V.M.add xvar 1 d_map, vars))
        else (from_var xvar, 1, (top_order, p_map, V.M.add xvar 1 d_map, xvar :: vars))
      | Add l ->
        let folder (sum, (top_o, pmap, dmap, vs)) ex = 
          let pure_ex, _, (top, m, d, new_vs) = aux (top_o, pmap, dmap, vs) ex in
          (add pure_ex sum, (top, m, d, new_vs))
        in
        let sum, (top_o, pmap, dmap, vs) = List.fold_left folder (from_const C.zero, (top_order, p_map, d_map, vars)) l in
        let get_deg_and_keep deg (_, mon) = 
          let mvars = get_vars_m mon in
          let get_mon_deg_and_keep v mdeg = 
            mdeg + ((get_degree v mon) * (V.M.find v dmap))
          in
          let mdeg = V.S.fold get_mon_deg_and_keep mvars 0 in
          (max mdeg deg)
        in
        let deg = List.fold_left get_deg_and_keep 0 (get_mons sum) in
        sum, deg, (top_o, pmap, dmap, vs)
      | Mult l -> 
        let folder (sum, deg, (top_o, pmap, dmap, vs)) ex = 
          let pure_ex, de, (top, m, d, new_vs) = aux (top_o, pmap, dmap, vs) ex in
          (mul pure_ex sum, deg + de, (top, m, d, new_vs))
        in
        List.fold_left folder (from_const C.one, 0, (top_order, p_map, d_map, vars)) l
      | Div (n, d) -> 
        let (pure_n, nd, (num_o, num_pmap, num_dmap, num_vars)) = aux (top_order, p_map, d_map, vars) n in
        let (pure_d, dd, (ord, pmap, dmap, vs)) = aux (num_o, num_pmap, num_dmap, num_vars) d in
        let new_variable = V.fresh_var () in
        let new_var_poly = from_var new_variable in
        (mul pure_n new_var_poly, nd + dd, (new_variable :: ord, S.add new_variable ("recip", pure_d) pmap, V.M.add new_variable dd dmap, vs))
      | Func (s, x) -> 
        let (pure_x, xd, (ord, pmap, dmap, vs)) = aux (top_order, p_map, d_map, vars) x in
        let new_variable = V.fresh_var () in
        (from_var new_variable, xd, (new_variable :: ord, S.add new_variable (s, pure_x) pmap, V.M.add new_variable xd dmap, vs))
      | Pow (base, exp) ->
        let (pure_base, bd, (ord, pmap, dmap, vs)) = aux (top_order, p_map, d_map, vars) base in
        let (pure_exp, ed, (ord, pmap, dmap, vs)) = aux (ord, pmap, dmap, vs) exp in
        match is_const pure_exp with
        | Some c ->
          (match C.to_int c with
          | Some i -> 
            if i >= 0 then (exp_poly pure_base i, bd * i, (ord, pmap, dmap, vs))
            else
              let neg_exp = (-1) * i in
              let new_variable = V.fresh_var () in
              let new_var_poly = from_var new_variable in
              (exp_poly new_var_poly neg_exp, bd * neg_exp, (new_variable :: ord, S.add new_variable ("recip", pure_base) pmap, V.M.add new_variable (bd * neg_exp) dmap, vs))
          | None ->
            failwith ("TODO add support for non-integer exponents"))
        | None ->
          (match is_const pure_base with
          | Some c ->
            let new_variable = V.fresh_var () in
            from_var new_variable, ed, (new_variable :: ord, S.add new_variable ("pow" ^ (C.to_string_c c), pure_exp) pmap, V.M.add new_variable ed dmap, vs)
          | None ->
            failwith "No support for multi-arity power funcs"
          )
      in
    let res_poly, _, (top_ord, pmap, dmap, vs) = aux ([], c.map, c.deg_map, c.non_dummy_vars) ex in
    let new_to = List.rev (List.fold_left (fun acc v -> if List.mem v acc then acc else v :: acc) top_ord (c.top_order)) in
    res_poly, {c with map = pmap; top_order = new_to; deg_map = dmap; non_dummy_vars = vs}



  let instantiate_eqs c =
    let recip_template = I.from_string "e f - 1" in
    let folder v (func, p) eqs = 
      if func = "recip" then
        substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) recip_template) :: eqs
      else eqs
    in
    S.fold folder c.map []

  let instantiate_ineqs c = 
    let floor_temp1, floor_temp2 = I.from_string "e - f", I.from_string "f + 1 - e" in
    let folder v (func, p) ineqs = 
      if func = "floor" then
        substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) floor_temp1)
        :: substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) floor_temp2)
         :: ineqs
      else ineqs
    in
    S.fold folder c.map []

  let instantiate_impls c =
    let template = (I.from_string "e", I.from_string "f") in
    let folder v (func, p) impls = 
        if func = "floor" || func = "recip" then
          (substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) (fst template)), substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) (snd template))) :: impls
        else impls
    in
    S.fold folder c.map []

  let effective_deg_ord deg_map keep_map const_map top_order a b =
    let a_vars = get_vars_m a in
    let b_vars = get_vars_m b in
    let (avd, bvd) = V.S.fold (fun v l -> (v, get_degree v a) :: l) a_vars [], V.S.fold (fun v l -> (v, get_degree v b) :: l) b_vars [] in
    let folder (rem_deg, keep_deg, const_deg) (v, d) = 
      if S.find v const_map then
        if V.M.mem v deg_map then (rem_deg, keep_deg, const_deg + d * (V.M.find v deg_map))
        else (rem_deg, keep_deg, const_deg + d)
      else if S.find v keep_map then 
        if V.M.mem v deg_map then (rem_deg, keep_deg + d * (V.M.find v deg_map), const_deg)
        else (rem_deg, keep_deg + d, const_deg)
      else
        if V.M.mem v deg_map then (rem_deg + d * (V.M.find v deg_map), keep_deg, const_deg)
        else (rem_deg + d, keep_deg, const_deg)
    in
    let ((a_rem_deg, a_keep_deg, a_const_deg), (b_rem_deg, b_keep_deg, b_const_deg)) = (List.fold_left folder (0, 0, 0) avd, List.fold_left folder (0, 0, 0) bvd) in
    if (a_rem_deg = b_rem_deg) then 
      if (a_keep_deg = b_keep_deg) then
        if (a_const_deg = b_const_deg) then
          let cmp_var (x, xe) (y, ye) = 
            if V.equal x y then Int.compare xe ye
            else 
              match (List.find_opt (fun (_, v) -> v = x) top_order, List.find_opt (fun (_, v) -> v = y) top_order) with
              | None, None -> V.compare x y
              | None, Some _ -> -1
              | Some _, None -> 1
              | Some (x_ind, _), Some (y_ind, _) -> Int.compare x_ind y_ind
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
        else Int.compare a_const_deg b_const_deg
      else Int.compare a_keep_deg b_keep_deg
    else Int.compare a_rem_deg b_rem_deg


  let equal_t_map a b = 
    let a_keys = fst (List.split (S.bindings a)) in
    let b_keys = fst (List.split (S.bindings b)) in
    if (List.sort V.compare a_keys) <> (List.sort V.compare b_keys) then
      false
    else
      let folder prev_eq v =
        if not prev_eq then prev_eq
        else 
          let a_term = S.find v a in
          let b_term = S.find v b in
          match (a_term, b_term) with
          | (a_fun , a_p), (b_fun, b_p) when a_fun = b_fun ->
            P.equal a_p b_p
          | _ -> false
      in
      List.fold_left folder true a_keys

  let eval func c = 
    if func = "recip" then Some (C.divc C.one c)
    else if func = "floor" then Some (C.floor c)
    else None

  let compute_deg_topo_keep_and_consts c = 
    let map = c.map in
    let folder v _ (dmap, kmap, topord, consts) =
      let rec process_var va dm km topo cons=         
        if V.M.mem va dm then (V.M.find va dm, V.M.find va km, V.M.find va cons, dm, km, topo, cons)
        else if not (S.mem va map) then 
          (1, S.find va km, false, V.M.add va 1 dm, km, topo, V.M.add va false cons)
        else
          let (_, p) = S.find va map in
          let (pd, p_keep, is_const, new_dm, new_km, new_topo, new_cons) = process_poly p dm km topo cons in
          if is_const then (0, p_keep, is_const, V.M.add va 1 new_dm, V.M.add va p_keep new_km, va :: new_topo, V.M.add va true new_cons)
          else
            (pd, p_keep, is_const, V.M.add va pd new_dm, V.M.add va p_keep new_km, va :: new_topo, V.M.add va false new_cons)
      and process_mon mon dm km topo cons = 
        let mon_vars = get_vars_m mon in
        let collect_vars va (deg, keep_mon, is_mon_const, dmacc, kmacc, topoacc, consacc) = 
          let (vad, va_keep, va_const, vadm, vakm, vatopo, vacons) = process_var va dmacc kmacc topoacc consacc in
          (vad * (get_degree va mon) + deg, va_keep && keep_mon, is_mon_const && va_const, vadm, vakm, vatopo, vacons)
        in
        V.S.fold collect_vars mon_vars (0, true, true, dm, km, topo, cons)
      and process_poly p dm km topo cons = 
        let mons = List.map snd (get_mons p) in
        let collect_mons (deg, keep_poly, is_poly_const, dmacc, kmacc, topoacc, consacc) m = 
          let (mad, ma_keep, ma_const, madm, makm, matopo, macons) = process_mon m dmacc kmacc topoacc consacc in
          (max deg mad, ma_keep && keep_poly, is_poly_const && ma_const, madm, makm, matopo, macons)
        in
        List.fold_left collect_mons (0, true, true, dm, km, topo, cons) mons
      in
      let (_, _, _, new_dm, new_km, new_topo, new_cons) = process_var v dmap kmap topord consts in
      (new_dm, new_km, new_topo, new_cons)
    in
    

    let (dmap, kmap, topo, consts) = S.fold folder map (V.M.empty, c.vars_to_keep, [], V.M.empty) in
    let dmap,  consts = List.fold_left (fun (dm, cs) nmv -> (P.V.M.add nmv 1 dm,  P.V.M.add nmv false cs)) (dmap, consts) c.non_dummy_vars in
    let topo = c.non_dummy_vars @ (List.rev topo) in
    {c with deg_map = dmap; constants = consts; top_order = topo; vars_to_keep = kmap}
      

  let reduce_modify p eliminated_vars processed_e_map ideal = 
    let rec aux to_red stable_e_map = 
      let to_red_vars = get_vars to_red in
      let folder var (red, semap) = 
        let (var_red, var_semap) = 
          if S.mem var semap then (S.find var semap, semap)
          else if S.mem var eliminated_vars then 
            let vred, new_map = aux (S.find var eliminated_vars) semap in
            vred, S.modify_def vred var (fun _ -> vred) new_map
          else 
            (fst (I.reduce (from_var var) ideal), semap)
        in
        (substitute (var, var_red) red, var_semap)
      in
      let (red, new_emap) = V.S.fold folder to_red_vars (to_red, stable_e_map) in
      let ired = fst (I.reduce red ideal) in
      (ired, new_emap)
    in
    aux p processed_e_map

  let reduce p cl = 
    let rec aux (to_red, red_occur) = 
      let to_red_vars = get_vars to_red in
      let folder var (red, red_occurd) = 
        let var_red, has_redu = 
          if S.mem var cl.eliminated_vars then aux (S.find var cl.eliminated_vars, true)
          else 
            let rem, reduc_occu = I.reduce (from_var var) cl.ideal in
            rem, reduc_occu || red_occurd
        in
        substitute (var, var_red) red, has_redu
      in
      let red, red_hap = V.S.fold folder to_red_vars (to_red, red_occur) in
      let i_red = I.reduce red cl.ideal in
      fst i_red, (snd i_red) || red_hap
    in
    aux (p, false)

  let reduce_only_map p eliminated_vars = 
    let rec aux to_red = 
      let to_red_vars = get_vars to_red in
      let folder var red = 
        let var_red = 
          if S.mem var eliminated_vars then aux (S.find var eliminated_vars)
          else from_var var
        in
        substitute (var, var_red) red
      in
      V.S.fold folder to_red_vars to_red
    in
    aux p

  let is_poly_const p = match is_const p with None -> false | Some _ -> true

  let close cl = 
    let rec aux old_map old_ideal c = 
      Log.log_line_s ~level:`trace "Computing closure";
      Log.log ~level:`trace pp_c (Some c);
      let eq_m = equal_t_map old_map c.map in
      let eq_i = I.equal old_ideal c.ideal in
      if eq_m && eq_i then c
      else
        let bindings = fst (List.split (S.bindings c.map)) in
        let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
        let pairs = get_pairs bindings in
        let new_eqs = 
          List.fold_left (fun acc (v1, v2) ->
            let smaller, bigger = if (I.get_ord c.ideal) (snd (make_mon_from_var v1 1)) (snd (make_mon_from_var v2 1)) < 0 then (v1, v2) else (v2, v1) in
            match S.find smaller c.map, S.find bigger c.map with
            | (func1, p1), (func2, p2) when func1 = func2 ->
              if P.equal p1 p2 then (smaller, bigger) :: acc
              else if I.mem (subtract p1 p2) c.ideal then (smaller, bigger) :: acc
              else acc
            | _ -> acc
          ) [] pairs in
        let remove_bigger (m, e, dm, km, cm) (smaller, bigger) = 
          (S.remove bigger m, S.add bigger (from_var smaller) e, S.remove bigger dm, S.remove bigger km, S.remove bigger cm) in
        let map, eliminated, dm, km, cm = List.fold_left remove_bigger (c.map, c.eliminated_vars, c.deg_map, c.vars_to_keep, c.constants) new_eqs in
        let reduce_map v (func, p) (m, stable_emap) = 
          let p_red, new_emap = reduce_modify p eliminated stable_emap c.ideal in
          S.add v (func, p_red) m, new_emap
        in
        let map, stable_emap = S.fold reduce_map map (S.empty, S.empty) in
        let updated_maps = compute_deg_topo_keep_and_consts {c with map; vars_to_keep = km; deg_map = dm; constants = cm} in
        let eliminate_vars v keep_var (m, semap, dm, km, cm) = 
          let is_map_var = S.mem v m in
          let v_red, newemap = reduce_modify (from_var v) eliminated semap c.ideal in
          let only_vars_to_keep = V.S.fold (fun v only_keep -> only_keep && (S.find v c.vars_to_keep)) (get_vars v_red) true in
          if is_poly_const v_red then
            if is_map_var then
              S.remove v m, S.add v v_red newemap, S.remove v dm, km, S.remove v cm
            else
              m, S.add v v_red newemap, S.remove v dm, km, S.remove v cm
          else if is_map_var then
            let (func, p) = S.find v m in
            match is_const p with
            | None -> 
              if only_vars_to_keep && not keep_var then
                S.remove v m, S.add v v_red newemap, S.remove v dm, km, S.remove v cm
              else
                m, newemap, dm, S.add v keep_var km, cm
            | Some c ->
              match eval func c with
              | None -> m, newemap, dm, S.add v keep_var km, cm
              | Some res -> S.remove v m, S.add v (from_const res) newemap, S.remove v dm, km, S.remove v cm
          else if only_vars_to_keep && not keep_var then
            S.remove v m, S.add v v_red newemap, S.remove v dm, km, S.remove v cm
          else
            m, newemap, dm, S.add v keep_var km, cm
        in
        let (new_m, new_elim, new_dm, new_km, new_cm) = S.fold eliminate_vars updated_maps.vars_to_keep (updated_maps.map, stable_emap, updated_maps.deg_map, S.empty, updated_maps.constants) in
        let eliminated = V.S.fold (fun v stable_map -> snd (reduce_modify (from_var v) eliminated stable_map c.ideal)) (V.S.diff (S.domain eliminated) (S.domain new_elim)) new_elim in
        let new_generators = List.map (fun p -> reduce_only_map p eliminated) (I.get_generators c.ideal) in
        let new_ideal =
          match I.get_implementation c.ideal with
          | `buch -> I.make_ideal (create_order (BatHashtbl.create 200) (effective_deg_ord new_dm new_km new_cm (List.mapi (fun i v -> (i, v)) updated_maps.top_order))) new_generators
          | `fgb -> I.make_ideal_f new_dm new_cm (List.mapi (fun i v -> (i, v)) updated_maps.top_order) new_generators
        in
        aux c.map c.ideal {map = new_m; eliminated_vars = eliminated; deg_map = new_dm; vars_to_keep = new_km; constants = new_cm; ideal = new_ideal; top_order = updated_maps.top_order; non_dummy_vars = updated_maps.non_dummy_vars}
    in
    aux S.empty (I.make_ideal lex_ord []) cl
        

  let unpurify p cl =
    let rec unpurify_var v =
      if S.mem v cl.map then 
        (let (func, p) = S.find v cl.map in
        let unpure_p = unpurify_poly p in
        match func with
        | s when s = "recip" ->
          Pow (unpure_p, Coe (C.of_int (-1)))
        | s ->
          Func (s, unpure_p))
      else
        Var (V.to_string v)
    and unpurify_mon (c, mon) = 
      let prod_list = V.S.fold (fun v acc -> Pow((unpurify_var v), Coe (C.of_int (get_degree v mon))) :: acc) (get_vars_m mon) [] in
      Mult (Coe c :: prod_list)
    and unpurify_poly poly = 
      Add (List.map unpurify_mon (get_mons poly))
    in
    unpurify_poly p
    

  let seed_vars_to_keep c vars_to_keep_l = 
    let seeded_kmap = List.fold_left (fun kmap v -> S.add v (List.mem v vars_to_keep_l) kmap) S.empty c.non_dummy_vars in
    {c with vars_to_keep = seeded_kmap}


  let make ?use_fgb:(fgb=true) eqs exprs = 
    let empty = if fgb then {ideal = I.make_ideal_f V.M.empty V.M.empty [] []; deg_map = V.M.empty; top_order = []; map = S.empty; constants = S.empty; eliminated_vars = S.empty; non_dummy_vars = []; vars_to_keep = S.empty} 
                else {ideal = I.make_ideal lex_ord []; map = S.empty; deg_map = V.M.empty; top_order = []; constants = S.empty; eliminated_vars = S.empty; non_dummy_vars = []; vars_to_keep = S.empty} 
    in
    let purify_all_exprs (pes, cl) ex = 
      let (pure_ex, new_cl) = purify ex cl in
      pure_ex :: pes, new_cl
    in
    let pure_exprs_rev, c = List.fold_left purify_all_exprs ([], empty) (eqs @ exprs) in
    let (_, given_eqs, pure_exprs) = List.fold_left (fun (i, es, exs) ex -> if i < List.length exprs then (i + 1, es, ex :: exs) else (i+1, ex :: es, exs)) (0, [], []) pure_exprs_rev in
    let instantiated_eqs = instantiate_eqs c in
    let c = {c with non_dummy_vars = List.sort V.compare c.non_dummy_vars} in

    Log.log_line_s ~level:`trace "Given eqs: ";
    Log.log ~level:`trace (Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) pp) (Some given_eqs);

    Log.log_line_s ~level:`trace "Instantiated eqs: ";
    Log.log ~level:`trace (Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) pp) (Some instantiated_eqs);

    let eqs = instantiated_eqs @ given_eqs in
    let c = compute_deg_topo_keep_and_consts (seed_vars_to_keep c []) in
    let new_ideal = match I.get_implementation c.ideal with
      | `buch -> I.make_ideal (create_order (BatHashtbl.create 200) (effective_deg_ord c.deg_map c.vars_to_keep c.constants (List.mapi (fun i v -> (i, v)) c.top_order))) eqs
      | `fgb -> I.make_ideal_f c.deg_map c.constants (List.mapi (fun i v -> (i, v)) c.top_order) eqs
    in
    let cl = { c with ideal = new_ideal} in
    let closed = close cl in
    let pure_exprs_red = List.map (fun p ->fst (reduce p closed)) pure_exprs in
    closed, pure_exprs_red

    open Sigs.Form

  let purify_form form clo = 
    let rec aux f cl = 
      match f with
      | Ge a -> 
        let poly, new_cl = purify a cl in
        Ge poly, [Ge poly], new_cl
      | Gt a -> 
        let poly, new_cl = purify a cl in
        Gt poly, [Gt poly], new_cl
      | Eq a ->
        let poly, new_cl = purify a cl in
        Eq poly, [Eq poly], new_cl
      | Or list ->
        let folder (proc, atoms, cur_cl) fo = 
          let (fo_poly, fo_atoms, new_cl) = aux fo cur_cl in
          (fo_poly :: proc, fo_atoms @ atoms, new_cl)
        in
        let p_list, atoms, new_cl = List.fold_left folder ([], [], cl) list in
        Or (List.rev p_list), atoms, new_cl
      | And list ->
        let folder (proc, atoms, cur_cl) fo = 
          let (fo_poly, fo_atoms, new_cl) = aux fo cur_cl in
          (fo_poly :: proc, fo_atoms @ atoms, new_cl)
        in
        let p_list, atoms, new_cl = List.fold_left folder ([], [], cl) list in
        And (List.rev p_list), atoms, new_cl
    in
    let pure_form, pure_atoms, cl = aux form clo in
    let c = compute_deg_topo_keep_and_consts (seed_vars_to_keep cl []) in
    let new_ideal = match I.get_implementation c.ideal with
      | `buch -> I.make_ideal (create_order (BatHashtbl.create 200) (effective_deg_ord c.deg_map c.vars_to_keep c.constants (List.mapi (fun i v -> (i, v)) c.top_order))) []
      | `fgb -> I.make_ideal_f c.deg_map c.constants (List.mapi (fun i v -> (i, v)) c.top_order) []
    in
    let cl = { c with ideal = new_ideal} in
    pure_form, pure_atoms, cl

  let add_eqs eqs cl = 
    Log.log_line_s ~level:`trace "starting to add eqs";
    let res = close {cl with ideal = I.add_eqs cl.ideal (List.map (fun p -> fst (reduce p cl)) eqs)} in
    Log.log_line_s ~level:`trace "finished adding eqs";
    res

  let get_ord cl = I.get_ord cl.ideal

  let get_generators cl = I.get_generators cl.ideal

  let set_order cl ord = 
    let gens = get_generators cl in
    let new_ideal = I.make_ideal ord gens in
    close ({cl with ideal = new_ideal})

  let set_effective_degree cl vars_to_keep = 
    let cl = compute_deg_topo_keep_and_consts (seed_vars_to_keep cl vars_to_keep) in
    let eff_ord = create_order (BatHashtbl.create 200) (effective_deg_ord cl.deg_map cl.vars_to_keep cl.constants (List.mapi (fun i v -> (i, v)) cl.top_order)) in
    set_order cl eff_ord

end
