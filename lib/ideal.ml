let (%) = BatPervasives.(%)


module Make (P : Poly.Polynomial) = struct

  include P

  type generators = 
    | Top (*<1>*)
    | Bot (*<0>*)
    | I of sorted_poly list (*<p1,...,pn>*)

  type impl = 
    | Buch
    | Fgb of (int V.M.map) * (bool V.M.map) * ((int * P.V.v) list)

  type ideal = {
    basis: generators;
    ord: monic_mon -> monic_mon -> int;
    impl:impl
  }

  let s_poly ord f g =
    let lcmlm = (C.from_string_c "1", lcm_of_mon (snd (lt f)) (snd (lt g))) in
    let f_m = divide_mon lcmlm (lt f) in
    let g_m = divide_mon lcmlm (lt g) in
    match (f_m, g_m) with
    | (Some f_t, Some g_t) ->
      let ftf = mult_mon_poly f_t (get_poly f) in
      subtracti ftf (mult_mon_poly g_t (get_poly g));
      make_sorted_poly ord ftf
    | _ -> failwith "shouldn't happen"


  let minimize fs = 
    let monic_grobner = List.map make_monic fs in
    let is_need poly l = 
      let divides x = match divide_mon (lt poly) (lt x) with | Some _ -> true | None -> false in
      not (List.exists divides l)
    in
    let rec filter prev rest =
      match rest with
      | [] -> prev
      | x :: xs ->
        if is_need x (prev @ xs) then 
          filter (x :: prev) xs
        else 
          filter prev xs
    in
    let min_basis = filter [] monic_grobner in
    if List.length min_basis = 0 then 
      Bot
    else if List.exists (fun p -> match is_const (get_poly p) with | Some _ -> true | None -> false) min_basis then
      Top
    else
      I min_basis

  let improved_buchberger ord fs prev_gb = 
    let rec aux worklist g =
      let t = (List.length g) - 1 in
      let criterion i j lcmu =
        let rec foo k =
          if k > t then false
          else if k = i || k = j then foo (k+1)
          else
            let p1 = if k < i then (k, i) else (i,k) in
            let p2 = if k < j then (k, j) else (j,k) in
            if List.exists ((=) p1) worklist then foo (k+1)
            else if List.exists ((=) p2) worklist then foo (k+1)
            else
              match divide_mon (lt (List.nth g k)) lcmu with
              | None -> foo (k+1)
              | Some _ -> true
        in
        foo 0
      in
      match worklist with
      | [] -> 
        {basis = minimize g; ord; impl = Buch}
      | (i, j) :: rest ->
        let (fi, fj) = (List.nth g i, List.nth g j) in
        let lcmlt = lcm_of_mon (snd (lt fi)) (snd (lt fj)) in (* lt or lm? *)
        let prod = (mult_mon (lt fi) (lt fj)) in
        if criterion i j (C.one, lcmlt) then aux rest g
        else if lex_ord lcmlt (snd prod) = 0 then aux rest g (* criterion *)
        else (
          let sp = s_poly ord fi fj in
          let (_, (_, s)) = division ord g sp in
          match is_const (get_poly s) with
          | Some c ->
            if C.cmp c (C.zero) = 0 then aux rest g
            else {basis = Top; ord; impl = Buch}
          | None ->
            aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) g)) (g @ [s])
        )
    in
    let norm_fs = prev_gb @ (List.map (make_sorted_poly ord) (List.rev (List.sort compare fs))) in
    let get_pairs l = List.filter (fun (x, y) -> x<>y && (x >= List.length prev_gb || y >= List.length prev_gb)) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    let norm_g = aux (get_pairs (List.mapi (fun i _ -> i) norm_fs)) norm_fs in
    norm_g

  let ppi f (i : ideal) = 
    Format.pp_open_hbox f ();
    Format.pp_print_string f "Ideal:";
    Format.print_space ();
    (match i.basis with
     | Top -> Format.pp_print_string f "<1>"
     | Bot -> Format.pp_print_string f "<0>"
     | I basis ->
        Format.pp_print_string f "<"; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ","; Format.pp_print_space fo ()) (pp ~ord:i.ord) f (List.map get_poly basis);
        Format.pp_print_string f ">";
        Format.pp_close_box f ());
    Format.pp_close_box f ()


  (*let pp_red ord f (p, basis, mults, rem) = 
    let filtered_list = List.filter_map (fun (m, b) -> if is_zero m then None else Some (m, b)) (List.combine mults basis) in
    let filtered_list = if List.length filtered_list = 0 then [from_const_s "0", from_const_s "0"] else filtered_list in
    (Format.pp_open_box f 0; (pp ~ord:ord) f p; 
    Format.pp_print_break f 1 4;
    Format.pp_print_string f "= ";
    Format.pp_open_hvbox f 0;
    (pp ~ord:ord) f rem; Format.pp_print_string f " +"; Format.pp_print_space f ();
    let pp_mb fo (m, b) = 
      Format.pp_open_box fo 0; 
      Format.pp_print_string fo "("; (pp ~ord:ord) fo m; Format.pp_print_string fo ")";
      Format.pp_print_break fo 1 4;
      Format.pp_print_string fo "("; (pp ~ord:ord) fo b; Format.pp_print_string fo ")";
      Format.pp_close_box fo ()
    in
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo " +"; Format.pp_print_space fo ()) pp_mb f filtered_list;
    Format.pp_close_box f (); Format.pp_close_box f ())*)

  let reduce p (i : ideal) : poly * bool = 
    match i.basis with
    | Top ->
      from_const_s "0", true
    | Bot -> p, false
    | I basis -> 
      let (reduction_occurred, (_, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      (*let (reduction_occurred, (mults, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      if not reduction_occurred then Log.log ~level:`trace (pp_red i.ord) None
      else Log.log ~level:`trace (pp_red i.ord) (Some (p, List.map fst basis, mults, fst rem));*)
      get_poly rem, reduction_occurred

  (*let reduce_just p (i : ideal) =
    match i.basis with
    | Top -> from_const_s "0", [from_const_s "1"]
    | Bot -> p, [from_const_s "0"]
    | I basis ->
      let (_, (mults, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      get_poly rem, mults*)


  let make_ideal ord eqs : ideal = 
    let normal = List.filter (not % is_zero) eqs in
    if List.length normal = 0 || List.for_all is_zero normal then 
      {basis = Bot; ord; impl = Buch}
    else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal then 
      {basis = Top; ord; impl = Buch}
    else 
      improved_buchberger ord normal []
     
  
  let make_grevlex_from_list hashtbl deg_map bk1 bk2 m1 m2 = 
    try BatHashtbl.find hashtbl (m1, m2) 
    with Not_found ->
      let res = 
        let effective_deg v = try V.M.find v deg_map with Not_found -> 1 in
        let m1d_bk_1 = List.map (fun v -> effective_deg v * get_degree v m1) bk1 in
        let m2d_bk_1 = List.map (fun v -> effective_deg v * get_degree v m2) bk1 in
        let m1bk1tot, m2bk1tot = List.fold_left (+) 0 m1d_bk_1, List.fold_left (+) 0 m2d_bk_1 in
        if m1bk1tot = m2bk1tot then
          let grevlex_bk1 = 
            try (List.find ((<>) 0) (List.rev (List.map2 (-) m1d_bk_1 m2d_bk_1)))
            with Not_found -> 0 in
          if grevlex_bk1 <> 0 then (-1) * grevlex_bk1
          else
            let m1d_bk_2 = List.map (fun v -> effective_deg v * get_degree v m1) bk2 in
            let m2d_bk_2 = List.map (fun v -> effective_deg v * get_degree v m2) bk2 in
            let m1bk2tot, m2bk2tot = List.fold_left (+) 0 m1d_bk_2, List.fold_left (+) 0 m2d_bk_2 in
            if m1bk2tot = m2bk2tot then
              try (-1) * (List.find ((<>) 0) (List.rev (List.map2 (-) m1d_bk_2 m2d_bk_2)))
              with Not_found -> 0
            else Int.compare m1bk2tot m2bk2tot
        else
          Int.compare m1bk1tot m2bk1tot
      in
      BatHashtbl.add hashtbl (m1, m2) res;
      BatHashtbl.add hashtbl (m2, m1) (-1*res);
      res

  let convert_to_faugere l (p : poly) = 
    let clearing_denom = 
      List.fold_left (fun acc (c,_)  -> Z.lcm (Q.den (C.to_zarith c)) acc) Z.one (get_mons p) in
    let mon_to_faugere (c, m) = 
      let md = List.map (fun v -> get_degree v m) l in
      let new_c = Q.num (Q.mul (C.to_zarith c) (Q.of_bigint clearing_denom)) in
      new_c, md
    in
    List.map mon_to_faugere (get_mons p)

  let convert_from_faugere l p = 
    from_mon_list (List.map (make_mon_from_faugere_mon l) p)

  let () = Faugere_zarith.Fgb_int_zarith.set_number_of_threads 2

  (*let pp_fpoly f (fpoly : (Z.t * int list) list) = 
    Format.pp_open_hvbox f 0;
    let pp_fmon fo (fmon : Z.t * int list) = 
      Format.pp_open_box fo 0;
      Format.pp_print_string fo (Z.to_string (fst fmon));
      Format.pp_print_string fo " * [";
      Format.pp_print_list ~pp_sep:(fun foo () -> Format.pp_print_string foo ";"; Format.pp_print_space foo ()) Format.pp_print_int fo (snd fmon);
      Format.pp_print_string fo "]";
      Format.pp_close_box fo ()
    in
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo " +"; Format.pp_print_space fo ()) pp_fmon f fpoly;
    Format.pp_close_box f ()

  let curr_var = ref 0

  let new_var () = 
    let y = "y_"^ (string_of_int !curr_var) in
    curr_var := !curr_var + 1;
    y*)
  
  let effective_deg_ord_as_list deg_map keep_map top_order ps = 
    let (keep_vars, discard_vars) = V.M.fold (fun v keep (keep_vars, discard_vars) -> if keep then (v :: keep_vars, discard_vars) else (keep_vars, v :: discard_vars)) keep_map ([], []) in
    let cmp_var x y =
      match (List.find_opt (fun (_, v) -> v = x) top_order, List.find_opt (fun (_, v) -> v = y) top_order) with
      | None, None -> (-1) *(V.compare x y)
      | Some (_, _), None -> 1
      | None, Some (_, _) -> (-1)
      | Some (x_ind, _), Some (y_ind, _) ->
        Int.compare x_ind y_ind
    in
    let var_ord_bk_1, var_ord_bk_2 = (List.rev (List.sort cmp_var discard_vars)), (List.rev (List.sort cmp_var keep_vars)) in
    let folder (svar_ord, svar_to_pvar_e, polys) pvar = 
      let pedeg = try V.M.find pvar deg_map with Not_found -> 1 in
      let svar = V.fresh_var () in
      let svar_edeg = from_var_pow svar pedeg in
      let sub_ps = List.map (substitute (pvar, svar_edeg)) polys in
      svar :: svar_ord, V.M.add svar (pvar, pedeg) svar_to_pvar_e, sub_ps
    in
    let rord_bk_1, svar_to_pvar, subps = List.fold_left folder ([], V.M.empty, ps) var_ord_bk_1 in
    let rord_bk_2, svar_to_pvar, subps = List.fold_left folder ([], svar_to_pvar, subps) var_ord_bk_2 in
    ((var_ord_bk_1, var_ord_bk_2), (List.rev rord_bk_1, List.rev rord_bk_2), svar_to_pvar, subps)


  let make_ideal_f deg_map keep_map top_ord eqs : ideal = 
    let normal = List.filter (fun p -> not (is_zero p)) eqs in
    let ((orig_vord_bk1, orig_vord_bk2), (vord_bk1, vord_bk2), svar_to_pvar, subps) = effective_deg_ord_as_list deg_map keep_map top_ord normal in
    let ord = make_grevlex_from_list (BatHashtbl.create 200) deg_map orig_vord_bk1 orig_vord_bk2 in
    if List.length normal = 0 || List.for_all is_zero normal then 
      {basis = Bot; ord; impl = Fgb (deg_map, keep_map, top_ord)}
    else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal then 
      {basis = Top; ord; impl = Fgb (deg_map, keep_map, top_ord)}
    else 
      let fpolys = List.map (convert_to_faugere (vord_bk1 @ vord_bk2)) subps in
      let gb = List.map (convert_from_faugere (vord_bk1 @ vord_bk2)) (Faugere_zarith.Fgb_int_zarith.fgb fpolys (List.map V.to_string vord_bk1) (List.map V.to_string vord_bk2)) in
      let mon_sub m = 
        let c, monic = fst m, snd m in 
        let folder v acc = 
          let vdeg = get_degree v monic in
          let (old_var, eff_deg) = V.M.find v svar_to_pvar in
          if vdeg mod eff_deg = 0 then 
            let new_deg = vdeg / eff_deg in
            mult_mon (make_mon_from_var old_var new_deg) acc
          else failwith "Not sure how to do this subtitution"
        in
        V.S.fold folder (get_vars_m monic) (make_mon_from_coef c)
      in
      let poly_sub p = 
        let mons = get_mons p in
        from_mon_list (List.map mon_sub mons)
      in
      let normal_gb = List.filter (fun p -> not (is_zero p)) gb in
      if List.length normal_gb = 0 || List.for_all is_zero normal_gb then {basis = Bot; ord; impl = Fgb (deg_map, keep_map, top_ord)}
      else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal_gb then {basis = Top; ord; impl = Fgb (deg_map, keep_map, top_ord)}
      else
        let sorted_gb = List.map (fun p -> make_sorted_poly ord (poly_sub p)) normal_gb in
        {basis = I sorted_gb; ord; impl = Fgb (deg_map, keep_map, top_ord)}

  let equal i1 i2 = 
    match i1.basis, i2.basis with
    | Bot, Bot -> true
    | Top, Top -> true
    | I b1, I b2 ->
      if List.length b1 <> List.length b2 then false
      else
        equal_sorted_sets b1 b2
    | _ -> false


  let mem p i =
    match i.basis with
    | Top -> true
    | Bot -> false
    | I _ -> is_zero (fst (reduce p i))

  let get_generators (i : ideal) : poly list = 
    match i.basis with
    | Top -> [from_const_s "1"]
    | Bot -> [from_const_s "0"]
    | I basis -> List.map get_poly basis

  let add_eqs i (new_eqs : poly list) =
    if new_eqs = [] then i
    else 
      match i.impl with
      | Fgb (deg_map, keep_map, top_order) ->
        make_ideal_f deg_map keep_map top_order ((get_generators i) @ new_eqs)
      | Buch ->
        match i.basis with
        | Top -> {basis = Top; ord = i.ord; impl = Buch}
        | Bot -> improved_buchberger i.ord new_eqs []
        | I gs -> improved_buchberger i.ord new_eqs gs

  let get_ord i = i.ord

  let get_implementation i = match i.impl with | Fgb _ -> `fgb | Buch -> `buch

end