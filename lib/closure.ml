module Make(P : Poly.Polynomial) = struct
  module I = Ideal.Make(P)
  module S = P.V.M

  include P
  
  open Sigs.Expr

  type closure = {
    ideal: I.ideal;
    map: (string * poly) S.map;
    keep_map: bool S.map;
    eliminated_vars: poly S.map;
    vars_to_keep: V.t list;
    vars_to_remove: V.t list
  }

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

    Format.pp_print_string f "Vars still to elim: ";
    Format.pp_print_break f 1 4; Format.pp_open_box f 0;
    Format.pp_print_string f "["; 
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) Format.pp_print_string f (List.map V.to_string c.vars_to_remove);
    Format.pp_print_string f "]"; Format.pp_close_box f (); Format.pp_print_space f ();

    I.ppi f c.ideal; Format.pp_print_space f (); Format.pp_close_box f ()
  

  let purify ex c old_to old_dmap old_kmap vars_to_remove =
    let rec aux (top_order, p_map, d_map, k_map, removes) e = 
      match e with
      | Coe x -> (from_const x, 0, true, (top_order, p_map, d_map, k_map, removes))
      | Var x -> 
        let xvar = V.of_string x in
        let keep = List.mem xvar c.vars_to_keep in
        if keep || List.mem xvar removes then (from_var xvar, 1, keep, (top_order, p_map, V.Mi.add xvar 1 d_map, S.add xvar keep k_map, removes))
        else (from_var xvar, 1, keep, (top_order, p_map, V.Mi.add xvar 1 d_map, S.add xvar keep k_map, xvar :: removes))
      | Add l ->
        let folder (sum, (top_o, pmap, dmap, kmap, rms)) ex = 
          let pure_ex, _, _, (top, m, d, k, r) = aux (top_o, pmap, dmap, kmap, rms) ex in
          (add pure_ex sum, (top, m, d, k, r))
        in
        let sum, (top_o, pmap, dmap, kmap, rms) = List.fold_left folder (from_const C.zero, (top_order, p_map, d_map, k_map, removes)) l in
        let get_deg_and_keep (deg, keep) (_, mon) = 
          let mvars = get_vars_m mon in
          let get_mon_deg_and_keep v (mdeg, mkeep) = 
            (mdeg + ((get_degree v mon) * (V.Mi.find v dmap)), mkeep && (S.find v kmap))
          in
          let mdeg, mkeep = V.S.fold get_mon_deg_and_keep mvars (0, true) in
          (max mdeg deg, mkeep && keep)
        in
        let deg, keep = List.fold_left get_deg_and_keep (0, true) (get_mons sum) in
        sum, deg, keep, (top_o, pmap, dmap, kmap, rms)
      | Mult l -> 
        let folder (sum, deg, keep, (top_o, pmap, dmap, kmap, rms)) ex = 
          let pure_ex, de, ke, (top, m, d, k, r) = aux (top_o, pmap, dmap, kmap, rms) ex in
          (mul pure_ex sum, deg + de, ke && keep, (top, m, d, k, r))
        in
        List.fold_left folder (from_const C.one, 0, true, (top_order, p_map, d_map, k_map, removes)) l
      | Div (n, d) -> 
        let (pure_n, nd, nk, (num_o, num_pmap, num_dmap, num_kmap, num_removes)) = aux (top_order, p_map, d_map, k_map, removes) n in
        let (pure_d, dd, dk, (ord, pmap, dmap, kmap, rms)) = aux (num_o, num_pmap, num_dmap, num_kmap, num_removes) d in
        let new_variable = V.fresh_var () in
        let new_var_poly = from_var new_variable in
        (mul pure_n new_var_poly, nd + dd, nk && dk, (new_variable :: ord, S.add new_variable ("recip", pure_d) pmap, V.Mi.add new_variable dd dmap, S.add new_variable (nk && dk) kmap, rms))
      | Floor x -> 
        let (pure_x, xd, xk, (ord, pmap, dmap, kmap, rms)) = aux (top_order, p_map, d_map, k_map, removes) x in
        let new_variable = V.fresh_var () in
        (from_var new_variable, xd, xk, (new_variable :: ord, S.add new_variable ("floor", pure_x) pmap, V.Mi.add new_variable xd dmap, S.add new_variable xk kmap, rms))
      | Pow (base, exp) ->
        let (pure_base, bd, bk, (ord, pmap, dmap, kmap, rms)) = aux (top_order, p_map, d_map, k_map, removes) base in
        if exp >= 0 then (exp_poly pure_base exp, bd * exp, bk, (ord, pmap, dmap, kmap, rms))
        else
          let neg_exp = (-1) * exp in
          let new_variable = V.fresh_var () in
          let new_var_poly = from_var new_variable in
          (exp_poly new_var_poly neg_exp, bd * neg_exp, bk, (new_variable :: ord, S.add new_variable ("recip", pure_base) pmap, V.Mi.add new_variable (bd * neg_exp) dmap, S.add new_variable bk kmap, rms))
      in
    let res_poly, _, _, (top_ord, pmap, dmap, kmap, rms) = aux ([], c.map, old_dmap, old_kmap, vars_to_remove) ex in
    let new_to = List.rev (List.fold_left (fun acc v -> if List.mem v acc then acc else v :: acc) top_ord old_to) in
    res_poly, {c with map = pmap}, new_to, dmap, kmap, rms

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
    let folder v (_, p) impls = 
        (substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) (fst template)), substitute (V.of_string "f", from_var v) (substitute (V.of_string "e", p) (snd template))) :: impls
    in
    S.fold folder c.map []

  let effective_deg_ord deg_map keep_map top_order a b =
    let a_vars = get_vars_m a in
    let b_vars = get_vars_m b in
    let (avd, bvd) = V.S.fold (fun v l -> (v, get_degree v a) :: l) a_vars [], V.S.fold (fun v l -> (v, get_degree v b) :: l) b_vars [] in
    let folder (rem_deg, keep_deg) (v, d) = 
      if S.find v keep_map then 
        if V.Mi.mem v deg_map then (rem_deg, keep_deg + d * (V.Mi.find v deg_map))
        else (rem_deg, keep_deg + d)
      else
        if V.Mi.mem v deg_map then (rem_deg + d * (V.Mi.find v deg_map), keep_deg)
        else (rem_deg + d, keep_deg)
    in
    let (a_deg, b_deg) = (List.fold_left folder (0, 0) avd, List.fold_left folder (0, 0) bvd) in
    if (fst a_deg = fst b_deg) then 
      if (snd a_deg = snd b_deg) then
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
      else Int.compare (snd a_deg) (snd b_deg)
    else Int.compare (fst a_deg) (fst b_deg)


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
            if P.equal a_p b_p then true
            else false
          | _ -> false
      in
      List.fold_left folder true a_keys

  let eval func c = 
    if func = "recip" then C.divc C.one c
    else if func = "floor" then C.floor c
    else failwith ("Don't know how to evaluate " ^ func)

  let compute_deg_and_keep map vars_to_keep = 
    let folder v _ (dmap, kmap, topo) =
      let rec process_var va dm km topo =         
        if V.Mi.mem va dm then (V.Mi.find va dm, S.find va km, dm, km, topo)
        else if not (S.mem va map) then 
          let keep = List.mem va vars_to_keep in (1, keep, V.Mi.add va 1 dm, S.add va keep km, topo)
        else
          let (_, p) = S.find va map in
          let (pd, keep, new_dm, new_km, new_topo) = process_poly p dm km topo in
          (pd, keep, V.Mi.add va pd new_dm, S.add va keep new_km, va :: new_topo)
      and process_mon mon dm km topo = 
        let mon_vars = get_vars_m mon in
        let collect_vars va (deg, keep, dmacc, kmacc, topoacc) = 
          let (vad, vak, vadm, vakm, vatopo) = process_var va dmacc kmacc topoacc in
          (vad * (get_degree va mon) + deg, vak && keep, vadm, vakm, vatopo)
        in
        V.S.fold collect_vars mon_vars (0, true, dm, km, topo)
      and process_poly p dm km topo = 
        let mons = List.map snd (get_mons p) in
        let collect_mons (deg, keep, dmacc, kmacc, topoacc) m = 
          let (mad, mak, madm, makm, matopo) = process_mon m dmacc kmacc topoacc in
          (max deg mad, mak && keep, madm, makm, matopo)
        in
        List.fold_left collect_mons (0, true, dm, km, topo) mons
      in
      let (_, _, new_dm, new_km, new_topo) = process_var v dmap kmap topo in
      (new_dm, new_km, new_topo)
    in
    let (dmap, kmap, topo) = S.fold folder map (V.Mi.empty, S.empty, []) in
    (dmap, kmap, List.rev topo)
      

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
            (I.reduce (from_var var) ideal, semap)
        in
        (substitute (var, var_red) red, var_semap)
      in
      let (red, new_emap) = V.S.fold folder to_red_vars (to_red, stable_e_map) in
      let ired = I.reduce red ideal in
      (ired, new_emap)
    in
    aux p processed_e_map

  let reduce p cl = 
    let rec aux to_red = 
      let to_red_vars = get_vars to_red in
      let folder var red = 
        let var_red = 
          if S.mem var cl.eliminated_vars then aux (S.find var cl.eliminated_vars)
          else 
            I.reduce (from_var var) cl.ideal
        in
        substitute (var, var_red) red
      in
      let red = V.S.fold folder to_red_vars to_red in
      I.reduce red cl.ideal
    in
    aux p

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


  let close cl = 
    let rec aux old_map old_ideal c = 
      Log.log_line_s ~level:`trace "Computing closure";
      Log.log ~level:`trace pp_c (Some c);
      if equal_t_map old_map c.map && I.equal old_ideal c.ideal then c
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
        let map, eliminated = List.fold_left (fun (m, e) (smaller, bigger) -> S.remove bigger m, S.add bigger (from_var smaller) e) (c.map, c.eliminated_vars) new_eqs in
        let reduce_map_and_elim_consts v (func, p) (m, stable_emap) = 
          let p_red, new_emap = reduce_modify p eliminated stable_emap c.ideal in
          match is_const p_red with
          | None -> S.add v (func, p_red) m, new_emap
          | Some c -> m, S.add v (from_const (eval func c)) new_emap
        in
        let map, stable_emap = S.fold reduce_map_and_elim_consts map (S.empty, S.empty) in
        let add_vars_to_remove (semap, vars_to_still_remove) var_to_remove = 
          let var_to_remove_red, newemap = reduce_modify (from_var var_to_remove) eliminated semap c.ideal in
          let only_vars_to_keep = V.S.fold (fun v only_keep -> only_keep && (S.find v c.keep_map)) (get_vars var_to_remove_red) true in
          if only_vars_to_keep then S.add var_to_remove var_to_remove_red newemap, vars_to_still_remove
          else newemap, var_to_remove :: vars_to_still_remove
        in
        let stable_emap, vars_still_to_remove = List.fold_left add_vars_to_remove (stable_emap, []) c.vars_to_remove in
        let eliminated = V.S.fold (fun v stable_map -> snd (reduce_modify (from_var v) eliminated stable_map c.ideal)) (V.S.diff (S.domain eliminated) (S.domain stable_emap)) stable_emap in
        let new_generators = List.map (fun p -> reduce_only_map p eliminated) (I.get_generators c.ideal) in
        let new_d_map, new_k_map, top_ord = compute_deg_and_keep map c.vars_to_keep in
        let new_d_map, new_k_map = List.fold_left (fun (dm, km) v -> V.Mi.add v 1 dm, S.add v false km) (new_d_map, new_k_map) vars_still_to_remove in
        let new_d_map, new_k_map = 
          List.fold_left (fun (dm, km) v -> 
            if not (S.mem v eliminated) && not (V.Mi.mem v dm) then V.Mi.add v 1 dm, S.add v true km
            else dm, km) 
            (new_d_map, new_k_map) 
            c.vars_to_keep 
        in
        let new_ideal =
          match I.get_implementation c.ideal with
          | `buch -> I.make_ideal (create_order (BatHashtbl.create 200) (effective_deg_ord new_d_map new_k_map (List.mapi (fun i v -> (i, v)) top_ord))) new_generators
          | `fgb -> I.make_ideal_f new_d_map new_k_map (List.mapi (fun i v -> (i, v)) top_ord) new_generators
        in
        let new_c = 
          {c with
            ideal = new_ideal;
            map;
            eliminated_vars = eliminated;
            vars_to_remove = vars_still_to_remove;
            keep_map = new_k_map;
          } 
        in
        aux c.map c.ideal new_c
    in
    aux S.empty (I.make_ideal lex_ord []) cl
        

  let unpurify p cl =
    let rec unpurify_var v =
      if S.mem v cl.map then 
        (let (func, p) = S.find v cl.map in
        let unpure_p = unpurify_poly p in
        match func with
        | s when s = "recip" ->
          Pow (unpure_p, -1)
        | s when s = "floor" ->
          Floor(unpure_p)
        | _ -> failwith ("Unknown function " ^ func))
      else
        Var (V.to_string v)
    and unpurify_mon (c, mon) = 
      let prod_list = V.S.fold (fun v acc -> (unpurify_var v) :: acc) (get_vars_m mon) [] in
      Mult (Coe c :: prod_list)
    and unpurify_poly poly = 
      Add (List.map unpurify_mon (get_mons poly))
    in
    unpurify_poly p
    

  let make ?use_fgb:(fgb=true) eqs exprs vars_to_keep = 
    let empty = if fgb then {ideal = I.make_ideal_f V.Mi.empty V.M.empty [] []; map = S.empty; keep_map = S.empty; eliminated_vars = S.empty; vars_to_keep = vars_to_keep; vars_to_remove = []} 
                else {ideal = I.make_ideal lex_ord []; map = S.empty; keep_map = S.empty; eliminated_vars = S.empty; vars_to_keep = vars_to_keep; vars_to_remove = []}
    in
    let purify_all_exprs (pes, cl, top, dm, km, rms) ex = 
      let (pure_ex, new_cl, new_to, new_dm, new_km, new_rms) = purify ex cl top dm km rms in
      pure_ex :: pes, new_cl, new_to, new_dm, new_km, new_rms
    in
    let pure_exprs_rev, c, top, dm, km, rms = List.fold_left purify_all_exprs ([], empty, [], V.Mi.empty, S.empty, []) (eqs @ exprs) in
    let (_, given_eqs, pure_exprs) = List.fold_left (fun (i, es, exs) ex -> if i < List.length exprs then (i + 1, es, ex :: exs) else (i+1, ex :: es, exs)) (0, [], []) pure_exprs_rev in
    let eqs = (instantiate_eqs c) @ given_eqs in
    let new_ideal = match I.get_implementation c.ideal with
      | `buch -> I.make_ideal (create_order (BatHashtbl.create 200) (effective_deg_ord dm km (List.mapi (fun i v -> (i, v)) top))) eqs
      | `fgb -> I.make_ideal_f dm km (List.mapi (fun i v -> (i, v)) top) eqs
    in
    let cl = 
      { c with
        ideal = new_ideal;
        vars_to_remove = rms;
        keep_map = km
      } in
    let closed = close cl in
    let pure_exprs_red = List.map (fun p ->reduce p closed) pure_exprs in
    closed, pure_exprs_red

  let add_eqs eqs cl = close {cl with ideal = I.add_eqs cl.ideal (List.map (fun p -> reduce p cl) eqs)}

  let get_ord cl = I.get_ord cl.ideal

end
