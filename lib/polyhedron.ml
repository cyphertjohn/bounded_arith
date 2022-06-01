module Make (C : Sigs.Coefficient) = struct

  let (%) = BatPervasives.(%)

  open Vpl__UserInterface.UncertifiedQ

 
  (*let vpl_poly_to_poly p =
    if is_bottom p then Bot
    else
      let add_vpl_cstr_to_p nep cstr =
        let const = C.of_zarith_q (Vpl.Cstr.Rat.get_c cstr) in
        let coef_map = List.fold_left (fun map (v, c) -> BatIMap.add (Vpl.Var.toInt v) (C.mulc (C.of_zarith_q c) (C.from_string_c "-1")) map) (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) (Vpl.Cstr.Rat.Vec.toList (Vpl.Cstr.Rat.get_v cstr)) in
        match cstr.typ with
        | Vpl.Cstr_type.Eq ->
          {nep with eqs = (coef_map, const) :: nep.eqs}
        | Vpl.Cstr_type.Le | Vpl.Cstr_type.Lt -> {nep with ineqs = (coef_map, const) :: nep.ineqs}
      in
      Ne (List.fold_left add_vpl_cstr_to_p {eqs = []; ineqs = []} (get_cstrs p))

  let poly_to_vpl_poly p = 
    match p with
    | Bot -> bottom
    | Ne cnstrs ->
      let mapper is_eq lterm = 
        let (cnstr_as_list, const) = BatIMap.fold (fun dim coef l -> (Q.neg (C.to_zarith coef), Vpl.Var.fromInt dim) :: l) (fst lterm) [], C.to_zarith (snd lterm) in
        if is_eq then Vpl.Cstr.Rat.eq cnstr_as_list const
        else Vpl.Cstr.Rat.le cnstr_as_list const
      in
      let vpl_cnstrs = (List.map (mapper true) cnstrs.eqs) @ (List.map (mapper false) cnstrs.ineqs) in
      let cond = Cond.of_cstrs vpl_cnstrs in
      assume (of_cond cond) top*)


  let negate_poly ctx polyhedron = 
    if is_bottom polyhedron then Z3.Boolean.mk_true ctx
    else
      let cstr_to_z3 cstr = 
        let rhs = Z3.Arithmetic.Real.mk_numeral_s ctx (Q.to_string (Vpl.Cstr.Rat.get_c cstr)) in
        let vpt_t_to_z3 (v, coef) = Z3.Arithmetic.mk_mul ctx [(Z3.Arithmetic.Real.mk_numeral_s ctx (Q.to_string coef)); Z3.Arithmetic.Real.mk_const ctx (Z3.Symbol.mk_int ctx (Vpl.Var.toInt v))] in
        let lhs = Z3.Arithmetic.mk_add ctx (List.map vpt_t_to_z3 (Vpl.Cstr.Rat.Vec.toList (Vpl.Cstr.Rat.get_v cstr))) in
        match cstr.typ with
        | Vpl.Cstr_type.Eq -> Z3.Boolean.mk_eq ctx lhs rhs
        | Vpl.Cstr_type.Le -> Z3.Arithmetic.mk_le ctx lhs rhs
        | Vpl.Cstr_type.Lt -> Z3.Arithmetic.mk_lt ctx lhs rhs
      in
      Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map cstr_to_z3 (get_cstrs polyhedron)))

  let z3_atom_to_poly negate phi = 
    let rec z3_term_to_dim_map t = 
      if Z3.Expr.is_const t then
        let dim = Z3.Symbol.get_int (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl t)) in
        (BatIMap.add dim C.one (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)), C.zero)
      else if Z3.Arithmetic.is_rat_numeral t then
        (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0), C.of_zarith_q (Z3.Arithmetic.Real.get_ratio t))
      else if Z3.Arithmetic.is_mul t then
        let (const, var) = List.partition (fun e -> Z3.Arithmetic.is_rat_numeral e) (Z3.Expr.get_args t) in
        if List.length var > 1 then failwith ("Non-linear formula: " ^ (Z3.Expr.to_string t))
        else 
          let const_term = List.fold_left (fun acc e -> C.mulc (C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)) acc) C.one const in
          if var = [] then (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0), const_term)
          else
            let dim = Z3.Symbol.get_int (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl (List.hd var))) in
            (BatIMap.add dim const_term (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)), C.zero)
      else if Z3.Arithmetic.is_add t then
        let sub_terms = List.map z3_term_to_dim_map (Z3.Expr.get_args t) in
        List.fold_left (fun (macc, constacc) (m, const) -> BatIMap.union C.addc macc m, C.addc constacc const) (List.hd sub_terms) (List.tl sub_terms)
      else
        failwith ("Unknown z3 term: " ^ (Z3.Expr.to_string t))
    in
    let lhs_cnstrm, lhs_const = z3_term_to_dim_map (List.nth (Z3.Expr.get_args phi) 0) in
    let rhs_cnstrm, rhs_const = z3_term_to_dim_map (List.nth (Z3.Expr.get_args phi) 1) in
    let merger _ _ l r = 
      match l, r with
      | Some lhs_c, None -> Some lhs_c
      | None, Some rhs_c -> Some (C.mulc rhs_c (C.from_string_c "-1"))
      | Some lhs_c, Some rhs_c -> Some (C.addc lhs_c (C.mulc rhs_c (C.from_string_c "-1")))
      | _ -> None
    in
    let lhs, rhs = BatIMap.merge merger lhs_cnstrm rhs_cnstrm, C.addc (C.mulc lhs_const (C.from_string_c "-1")) rhs_const in  (* lhs <=> rhs *)
    if ((not negate) && (Z3.Arithmetic.is_ge phi || Z3.Arithmetic.is_gt phi)) || (negate && (Z3.Arithmetic.is_le phi || Z3.Arithmetic.is_lt phi)) then
      let (vpl_map, vpl_const) = BatIMap.fold (fun dim coef l -> (Q.neg (C.to_zarith coef), Vpl.Var.fromInt dim) :: l) lhs [], Q.neg (C.to_zarith rhs) in
      if Z3.Arithmetic.is_ge phi || (negate && Z3.Arithmetic.is_lt phi) then [Vpl.Cstr.Rat.le vpl_map vpl_const]
      else [Vpl.Cstr.Rat.lt vpl_map vpl_const]
    else if negate && Z3.Boolean.is_eq phi then
      let (vpl_map_gt, vpl_const_gt) = BatIMap.fold (fun dim coef l -> (Q.neg (C.to_zarith coef), Vpl.Var.fromInt dim) :: l) lhs [], Q.neg (C.to_zarith rhs) in
      let (vpl_map_lt, vpl_const_lt) = BatIMap.fold (fun dim coef l -> (C.to_zarith coef, Vpl.Var.fromInt dim) :: l) lhs [], C.to_zarith rhs in
      [Vpl.Cstr.Rat.lt vpl_map_gt vpl_const_gt; Vpl.Cstr.Rat.lt vpl_map_lt vpl_const_lt]
    else
      let (vpl_map, vpl_const) = BatIMap.fold (fun dim coef l -> (C.to_zarith coef, Vpl.Var.fromInt dim) :: l) lhs [], C.to_zarith rhs in
      if Z3.Arithmetic.is_le phi || (negate && Z3.Arithmetic.is_gt phi) then [Vpl.Cstr.Rat.le vpl_map vpl_const]
      else if Z3.Arithmetic.is_lt phi || (negate && Z3.Arithmetic.is_ge phi) then [Vpl.Cstr.Rat.lt vpl_map vpl_const]
      else if Z3.Boolean.is_eq phi && (not negate) then [Vpl.Cstr.Rat.eq vpl_map vpl_const]
      else failwith "All cases should have been covered"


  type lterm = C.coef BatIMap.t * C.coef

  let cntsr_to_z3 kind ctx c =
    let term_to_z3 dim coef = 
      Z3.Arithmetic.mk_mul ctx [Z3.Arithmetic.Real.mk_numeral_s ctx (C.to_string_c coef); Z3.Arithmetic.Real.mk_const ctx (Z3.Symbol.mk_int ctx dim)]
    in
    let lhs = Z3.Arithmetic.mk_add ctx (BatIMap.fold (fun dim coef acc -> (term_to_z3 dim coef) :: acc) (fst c) [Z3.Arithmetic.Real.mk_numeral_s ctx (C.to_string_c (snd c))]) in
    match kind with
    | `eq -> Z3.Boolean.mk_eq ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
    | `ge -> Z3.Arithmetic.mk_ge ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
    | `gt -> Z3.Arithmetic.mk_gt ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)

  let lt_eq a b = 
    if not (C.cmp (snd a) (snd b) = 0) then false
    else 
      let merger _ _ a_opt b_opt = 
        match a_opt, b_opt with
        | None, Some _ -> b_opt
        | Some _, None -> a_opt
        | None, None -> None
        | Some a_coef, Some b_coef when C.cmp a_coef b_coef = 0 -> None
        | _ -> a_opt
      in
      BatIMap.is_empty (BatIMap.merge merger (fst a) (fst b))

  let pp_l f lt = 
    if BatIMap.is_empty (fst lt) then (Format.pp_open_hbox f (); Format.pp_print_string f (C.to_string_c (snd lt)); Format.pp_close_box f ())
    else 
      let tlist = BatIMap.fold 
        (fun dim coef l -> 
          if C.cmp coef C.zero < 0 then (C.to_string_c (C.mulc coef (C.from_string_c "-1")) ^ ".v" ^ (string_of_int dim), true) :: l
          else (C.to_string_c coef ^ ".v" ^ (string_of_int dim), false) :: l) (fst lt) [] in
      let tlist = 
        if C.cmp (snd lt) C.zero < 0 then List.rev ((C.to_string_c (C.mulc (C.from_string_c "-1") (snd lt)), true) :: tlist)
        else if C.cmp (snd lt) C.zero = 0 then List.rev tlist
        else List.rev ((C.to_string_c (snd lt), false) :: tlist)
      in
      let ft, is_ft_neg = List.hd tlist in
      Format.pp_open_hbox f ();
      if is_ft_neg then Format.pp_print_string f ("-" ^ ft)
      else Format.pp_print_string f ft;
      let print_t (t, is_neg) = 
        if is_neg then (Format.pp_print_string f " -"; Format.pp_print_space f ())
        else (Format.pp_print_string f " +"; Format.pp_print_space f ());
        Format.pp_print_string f t
      in
      List.iter print_t (List.tl tlist); Format.pp_close_box f ()


  type ne_poly = {eqs: lterm list; non_strict: lterm list; strict: lterm list}

  type polyhedron = | Bot | Ne of ne_poly

  let is_cnstr_mem poly kind cnstr = 
    match poly with
    | Bot -> false
    | Ne p ->
      match kind with
      | `eq -> List.exists (lt_eq cnstr) p.eqs
      | `ge -> List.exists (lt_eq cnstr) p.non_strict
      | `gt -> List.exists (lt_eq cnstr) p.strict

  let pp f p = 
    match p with
    | Bot -> Format.pp_print_string f "Bot"
    | Ne cnstrs ->
      let pp_print_eq fo eq = 
        Format.pp_open_hbox fo (); pp_l fo eq; Format.pp_print_string fo " = 0"; Format.pp_close_box fo ()
      in
      let pp_print_ge fo ge = 
        Format.pp_open_hbox fo (); pp_l fo ge; Format.pp_print_string fo " >= 0"; Format.pp_close_box fo ()
      in
      let pp_print_gt fo gt = 
        Format.pp_open_hbox fo (); pp_l fo gt; Format.pp_print_string fo " > 0"; Format.pp_close_box fo ()
      in
      Format.pp_open_vbox f 0;
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_eq f cnstrs.eqs;
      Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_ge f cnstrs.non_strict;
      Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_gt f cnstrs.strict;
      Format.pp_close_box f ()


  let get_poly_vars p = 
    match p with
    | Bot -> BatISet.empty
    | Ne poly ->
      let folder set cnstr = BatISet.union (BatIMap.domain (fst cnstr)) set in
      List.fold_left folder (List.fold_left folder (List.fold_left folder BatISet.empty poly.eqs) poly.non_strict) poly.strict

  let poly_to_vpl_poly p = 
    match p with
    | Bot -> bottom
    | Ne cnstrs ->
      let map_to_vpl m = BatIMap.fold (fun dim coef l -> (Q.neg (C.to_zarith coef), Vpl.Var.fromInt dim) :: l) m [] in
      let vpl_eqs = List.map (fun (m, c) -> Vpl.Cstr.Rat.eq (map_to_vpl m) (C.to_zarith c)) cnstrs.eqs in
      let vpl_non_strict = List.map (fun (m, c) -> Vpl.Cstr.Rat.le (map_to_vpl m) (C.to_zarith c)) cnstrs.non_strict in
      let vpl_strict = List.map (fun (m, c) -> Vpl.Cstr.Rat.lt (map_to_vpl m) (C.to_zarith c)) cnstrs.strict in
      assume (of_cond (Cond.of_cstrs (vpl_eqs @ vpl_non_strict @ vpl_strict))) top

  let vpl_poly_to_poly p =
    if is_bottom p then Bot
    else
      let add_vpl_cstr_to_p nep cstr =
        let const = C.of_zarith_q (Vpl.Cstr.Rat.get_c cstr) in
        let coef_map = List.fold_left (fun map (v, c) -> BatIMap.add (Vpl.Var.toInt v) (C.mulc (C.of_zarith_q c) (C.from_string_c "-1")) map) (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) (Vpl.Cstr.Rat.Vec.toList (Vpl.Cstr.Rat.get_v cstr)) in
        match cstr.typ with
        | Vpl.Cstr_type.Eq ->
          {nep with eqs = (coef_map, const) :: nep.eqs}
        | Vpl.Cstr_type.Le -> 
          {nep with non_strict = (coef_map, const) :: nep.eqs}
        | Vpl.Cstr_type.Lt -> 
          {nep with strict = (coef_map, const) :: nep.strict}
      in
      Ne (List.fold_left add_vpl_cstr_to_p {eqs = []; non_strict = []; strict = []} (get_cstrs p))


  let z3_atom_to_polyhedron negate phi = 
    let rec z3_term_to_dim_map t = 
      if Z3.Expr.is_const t then
        let dim = Z3.Symbol.get_int (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl t)) in
        (BatIMap.add dim C.one (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)), C.zero)
      else if Z3.Arithmetic.is_rat_numeral t then
        (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0), C.of_zarith_q (Z3.Arithmetic.Real.get_ratio t))
      else if Z3.Arithmetic.is_mul t then
        let (const, var) = List.partition (fun e -> Z3.Arithmetic.is_rat_numeral e) (Z3.Expr.get_args t) in
        if List.length var > 1 then failwith ("Non-linear formula: " ^ (Z3.Expr.to_string t))
        else 
          let const_term = List.fold_left (fun acc e -> C.mulc (C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)) acc) C.one const in
          if var = [] then (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0), const_term)
          else
            let dim = Z3.Symbol.get_int (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl (List.hd var))) in
            (BatIMap.add dim const_term (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)), C.zero)
      else if Z3.Arithmetic.is_add t then
        let sub_terms = List.map z3_term_to_dim_map (Z3.Expr.get_args t) in
        List.fold_left (fun (macc, constacc) (m, const) -> BatIMap.union C.addc macc m, C.addc constacc const) (List.hd sub_terms) (List.tl sub_terms)
      else
        failwith ("Unknown z3 term: " ^ (Z3.Expr.to_string t))
    in
    let lhs_cnstrm, lhs_const = z3_term_to_dim_map (List.nth (Z3.Expr.get_args phi) 0) in
    let rhs_cnstrm, rhs_const = z3_term_to_dim_map (List.nth (Z3.Expr.get_args phi) 1) in
    let merger _ _ l r = 
      match l, r with
      | Some lhs_c, None -> Some lhs_c
      | None, Some rhs_c -> Some (C.mulc rhs_c (C.from_string_c "-1"))
      | Some lhs_c, Some rhs_c -> Some (C.addc lhs_c (C.mulc rhs_c (C.from_string_c "-1")))
      | _ -> None
    in
    let term, const = BatIMap.merge merger lhs_cnstrm rhs_cnstrm, C.addc (C.mulc rhs_const (C.from_string_c "-1")) lhs_const in  (* lhs + rhs <=> 0 *)
    if ((not negate) && (Z3.Arithmetic.is_ge phi || Z3.Arithmetic.is_gt phi)) || (negate && (Z3.Arithmetic.is_le phi || Z3.Arithmetic.is_lt phi)) then
      if Z3.Arithmetic.is_ge phi || (negate && Z3.Arithmetic.is_lt phi) then {eqs = []; non_strict = [(term, const)]; strict = []}
      else {eqs = []; non_strict = []; strict = [(term, const)]}
    else if negate && Z3.Boolean.is_eq phi then
      let lt_zero_m, lt_zero_c = BatIMap.map (C.mulc (C.from_string_c "-1")) term, C.mulc (C.from_string_c "-1") const in
      {eqs = []; non_strict = []; strict = [(term, const); (lt_zero_m, lt_zero_c)]}
    else if Z3.Boolean.is_eq phi then {eqs = [term, const]; non_strict = []; strict = []}
    else
      let lt_zero_m, lt_zero_c = BatIMap.map (C.mulc (C.from_string_c "-1")) term, C.mulc (C.from_string_c "-1") const in
      if Z3.Arithmetic.is_le phi || (negate && Z3.Arithmetic.is_gt phi) then {eqs = []; non_strict = [(lt_zero_m, lt_zero_c)]; strict = []}
      else if Z3.Arithmetic.is_lt phi || (negate && Z3.Arithmetic.is_ge phi) then {eqs = []; non_strict = []; strict = [(lt_zero_m, lt_zero_c)]}
      else failwith "All cases should have been covered"

  let meet x y = 
    match x, y with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Ne a, Ne b ->
      Ne {eqs = a.eqs @ b.eqs; non_strict = a.non_strict @ b.non_strict; strict = a.strict @ b.strict}

  let top_p = Ne {eqs = []; non_strict = []; strict = []}


  let remove_dummy_cnstrs p = 
    match p with
    | Bot -> Bot
    | Ne cnstrs ->
      let filter_map m = BatIMap.fold (fun dim coef map -> if C.cmp coef C.zero = 0 then map else BatIMap.add dim coef map) m (BatIMap.empty ~eq:(fun _ _ -> false)) in
      let filter_eqs filtered (tmap, const) = 
        match filtered with
        | None -> None
        | Some l ->
          let filtered_map = filter_map tmap in
          if BatIMap.is_empty filtered_map && C.cmp const C.zero = 0 then Some l
          else if BatIMap.is_empty filtered_map then None
          else Some ((filtered_map, const) :: l)
      in
      let filter_ineqs strict filtered (tmap, const) = 
        match filtered with
        | None -> None
        | Some l -> 
          let filtered_map = filter_map tmap in
          if BatIMap.is_empty filtered_map && ((C.cmp const C.zero = 0 && (not strict)) || C.cmp const C.zero > 0) then Some l
          else if BatIMap.is_empty filtered_map then None
          else Some ((filtered_map, const) :: l)
      in
      match List.fold_left filter_eqs (Some []) cnstrs.eqs with
      | None -> Bot
      | Some eqs ->
        match List.fold_left (filter_ineqs false) (Some []) cnstrs.non_strict with
        | None -> Bot
        | Some non_strict ->
          match List.fold_left (filter_ineqs true) (Some []) cnstrs.strict with
          | None -> Bot
          | Some strict -> Ne {eqs; non_strict; strict}


  type vt = | MinusInf | Term of (C.coef BatIMap.t * C.coef) | TermEp of (C.coef BatIMap.t * C.coef)

  let project_dim m polyhedron d = 
    match polyhedron with | Bot -> Bot | Ne p -> let (eqs, non_strict, strict) = p.eqs, p.non_strict, p.strict in
    let vt = 
      let merge_vt x y =
        match x, y with
        | None, x | x, None -> x
        | Some (_, value, _), Some (_, value', _) when C.cmp value value' < 0 -> y
        | Some (_, value, _), Some (_, value', _) when C.cmp value value' > 0 -> x
        | Some (_, _, _), Some (_, _, true) -> y
        | _ -> x
      in
      let search_eq_terms found (map, const) = 
        match found with
        | Some _ -> found
        | None -> 
          if BatIMap.mem d map then
            let d_coef = BatIMap.find d map in
            if C.cmp d_coef C.zero = 0 then None
            else Some (BatIMap.map (fun coef -> C.mulc (C.divc coef d_coef) (C.from_string_c "-1")) (BatIMap.remove d map), C.mulc (C.from_string_c "-1") (C.divc const d_coef))
          else None
      in
      match List.fold_left search_eq_terms None eqs with
      | Some t -> Term t
      | None ->
        let folder is_strict vt (vmap, const) = 
          let d_coef = try BatIMap.find d vmap with Not_found -> C.zero in
          if C.cmp d_coef C.zero <= 0 then vt
          else
            let lower_b = BatIMap.map (fun coef -> C.divc (C.mulc (C.from_string_c "-1") coef) d_coef) (BatIMap.remove d vmap),  C.divc (C.mulc (C.from_string_c "-1") const) d_coef in
            let lower_b_interp = BatIMap.fold (fun lb_dim coef v -> C.addc v (C.mulc coef (BatIMap.find lb_dim m))) (fst lower_b) (snd lower_b) in
            merge_vt vt (Some (lower_b, lower_b_interp, is_strict))
        in
        match List.fold_left (folder true) (List.fold_left (folder false) None non_strict) strict with
        | None -> MinusInf
        | Some (t, _, is_strict) when not is_strict -> Term t
        | Some (t, _, _) -> TermEp t
    in
    match vt with
    | Term t ->
      let folder c_list (c_map, const) = 
        if not (BatIMap.mem d c_map) then (c_map, const) :: c_list
        else
          let d_coef = BatIMap.find d c_map in (* substitute  d = (fst t) + (snd t)  into  c_map + const >=> 0 *)
          let new_map = 
            if C.cmp d_coef C.zero = 0 then BatIMap.remove d c_map
            else BatIMap.remove d (BatIMap.union C.addc (BatIMap.map (C.mulc d_coef) (fst t)) c_map) in
          let new_const = C.addc (C.mulc d_coef (snd t)) const in
          (new_map, new_const) :: c_list
      in
      let eqs, non_strict, strict = (List.fold_left folder [] eqs, List.fold_left folder [] non_strict, List.fold_left folder [] strict) in
      Ne {eqs; non_strict; strict}
    | MinusInf -> (* None represents bottom *)
      let fold_eqs es (c_map, const) = 
        match es with
        | None -> None
        | Some l -> 
          if not (BatIMap.mem d c_map) then Some ((c_map, const) :: l)
          else
            if C.cmp (BatIMap.find d c_map) C.zero = 0 then Some ((BatIMap.remove d c_map, const) :: l)
            else None
      in
      let fold_ineqs strict poly (c_map, const) = 
        match poly with | None -> None
        | Some cnstrs ->
          if not (BatIMap.mem d c_map) then Some ((c_map, const) :: cnstrs)
          else if C.cmp (BatIMap.find d c_map) C.zero = 0 then
            let new_map = BatIMap.remove d c_map in
            if BatIMap.is_empty new_map && (C.cmp const C.zero > 0 || ((not strict) && C.cmp const C.zero = 0)) then poly
            else if BatIMap.is_empty new_map then None
            else Some ((new_map, const) :: cnstrs)
          else
            if C.cmp (BatIMap.find d c_map) C.zero > 0 then None
            else poly
      in
      (match List.fold_left fold_eqs (Some []) eqs with
      | None -> Bot
      | Some eqs ->
        (match List.fold_left (fold_ineqs false) (Some []) non_strict with
        | None -> Bot
        | Some non_strict ->
          (match List.fold_left (fold_ineqs true) (Some []) strict with
          | None -> Bot
          | Some strict -> Ne {eqs; non_strict; strict}
          )))
    | TermEp t -> 
      let fold_eqs es (c_map, const) = 
        match es with
        | None -> None
        | Some l -> 
          if not (BatIMap.mem d c_map) then Some ((c_map, const) :: l)
          else
            if C.cmp (BatIMap.find d c_map) C.zero = 0 then Some ((BatIMap.remove d c_map, const) :: l)
            else None
      in
      let fold_ineqs strict (nstrct, strct) (c_map, const) = 
        if not (BatIMap.mem d c_map) && strict then nstrct, (c_map, const) :: strct
        else if not (BatIMap.mem d c_map) then (c_map, const) :: nstrct, strct
        else 
          let d_coef = BatIMap.find d c_map in
          if C.cmp d_coef C.zero = 0 && strict then nstrct, (BatIMap.remove d c_map, const) :: strct
          else if C.cmp d_coef C.zero = 0 then (BatIMap.remove d c_map, const) :: nstrct, strct
          else
            let new_map = BatIMap.remove d (BatIMap.union C.addc (BatIMap.map (C.mulc d_coef) (fst t)) c_map) in
            let new_const = C.addc (C.mulc d_coef (snd t)) const in
            if C.cmp C.zero d_coef < 0 then (new_map, new_const) :: nstrct, strct
            else nstrct, (new_map, new_const) :: strct
      in
      match List.fold_left fold_eqs (Some []) eqs with
      | None -> Bot
      | Some eqs -> 
        let non_strict, strict = List.fold_left (fold_ineqs true) (List.fold_left (fold_ineqs false) ([], []) non_strict) strict in
        Ne {eqs; non_strict; strict}
          
  (*if is_bottom p then failwith "Projecting on a bottom polyhedron"
    else
      let convert_cstrs (eqs, non_strict_ineqs, strict_ineqs) cstr = 
        let map = List.fold_left (fun ma (var, coef) -> BatIMap.add (Vpl.Var.toInt var) (C.of_zarith_q (Q.neg coef)) ma) (BatIMap.empty ~eq:(fun _ _ -> false)) (Vpl.Cstr.Rat.Vec.toList (Vpl.Cstr.Rat.get_v cstr)) in
        let const = C.of_zarith_q (Vpl.Cstr.Rat.get_c cstr) in
        match cstr.typ with
        | Vpl.Cstr_type.Eq -> (map, const) :: eqs, non_strict_ineqs, strict_ineqs
        | Vpl.Cstr_type.Le -> eqs, (map, const) :: non_strict_ineqs, strict_ineqs
        | Vpl.Cstr_type.Lt -> eqs, non_strict_ineqs, (map, const) :: strict_ineqs
      in
      (* Each constraint is ax + b = || >= || > 0 *)
      let eqs, non_strict, strict = List.fold_left convert_cstrs ([], [], []) (get_cstrs p) in*)


  let local_project model project_dims p =
    let m = 
        List.fold_left (fun map fun_decl -> 
          if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then map (* Not a general solution *)
          else
            let interp = match Z3.Model.get_const_interp model fun_decl with
            | None -> failwith "Const has no interpretation in model"
            | Some e-> 
              C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
            in
            BatIMap.add (Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl)) interp map) (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) (Z3.Model.get_const_decls model) in
    remove_dummy_cnstrs (List.fold_left (project_dim m) p project_dims)


  (*let local_project model project_dims p =
    if is_bottom p then p
    else 
      let partition_constraints (eqs, nstrict, strict) cstr = 
        let vmap = List.fold_left (fun m (v, coef) -> BatIMap.add (Vpl.Var.toInt v) (C.of_zarith_q (Q.neg coef)) m) (BatIMap.empty ~eq:(fun _ _ -> false)) (Vpl.Cstr.Rat.Vec.toList (Vpl.Cstr.Rat.get_v cstr)) in
        let const = C.of_zarith_q (Vpl.Cstr.Rat.get_c cstr) in
        match cstr.typ with
        | Vpl.Cstr_type.Eq -> (vmap, const) :: eqs, nstrict, strict
        | Vpl.Cstr_type.Le -> eqs, (vmap, const) :: nstrict, strict
        | Vpl.Cstr_type.Lt -> eqs, nstrict, (vmap, const) :: strict
      in
      let projection = local_project_i model project_dims (List.fold_left partition_constraints ([], [], []) (get_cstrs p)) in
      match projection with
      | None -> bottom
      | Some (eqs, non_strict, strict) ->
        let imap_to_cstr_v map = 
          BatIMap.fold (fun dim coef l -> (Q.neg (C.to_zarith coef), Vpl.Var.fromInt dim) :: l) map []
        in
        let eq_cnstrs = List.map (fun (map, const) -> Vpl.Cstr.Rat.eq (imap_to_cstr_v map) (C.to_zarith const)) eqs in
        let non_strict_cnstrs = List.map (fun (map, const) -> Vpl.Cstr.Rat.le (imap_to_cstr_v map) (C.to_zarith const)) non_strict in
        let strict_cnstrs = List.map (fun (map, const) -> Vpl.Cstr.Rat.lt (imap_to_cstr_v map) (C.to_zarith const)) strict in
        assume (of_cond (Cond.of_cstrs (eq_cnstrs @ non_strict_cnstrs @ strict_cnstrs))) top*)
  

  let generalize_model model projected_dims form = 
    let rec get_implicant negate phi = 
      if Z3.Boolean.is_and phi then
        let get_and_check_child_impls processed_children child = 
          match processed_children with
          | Bot -> Bot
          | Ne p ->
            match get_implicant negate child with
            | Bot -> Bot
            | Ne new_cs -> meet (Ne p) (Ne new_cs)
        in
        List.fold_left get_and_check_child_impls top_p (Z3.Expr.get_args phi)
      else if Z3.Boolean.is_or phi then
        let find_child_impl found child =
          match found with
          | Ne _ -> found
          | Bot -> get_implicant negate child
        in
        List.fold_left find_child_impl Bot (Z3.Expr.get_args phi)
      else if Z3.Boolean.is_not phi then
        get_implicant (not negate) (List.nth (Z3.Expr.get_args phi) 0)
      else if Z3.Boolean.is_implies phi then
        match get_implicant (not negate) (List.nth (Z3.Expr.get_args phi) 0) with
        | Ne c_list -> Ne c_list
        | Bot -> get_implicant negate (List.nth (Z3.Expr.get_args phi) 1)
      else if Z3.Arithmetic.is_ge phi || Z3.Arithmetic.is_gt phi || Z3.Arithmetic.is_le phi || Z3.Arithmetic.is_lt phi || Z3.Boolean.is_eq phi then
        let models_sats = 
          let t_interp = 
            match Z3.Model.eval model phi false with
            | None -> failwith "Error evaluating model"
            | Some e -> Z3.Boolean.is_true e
          in
          if negate then not t_interp
          else t_interp
        in
        if models_sats then
          Ne (z3_atom_to_polyhedron negate phi)  
        else Bot
      else failwith ("Unknown formula node: " ^ (Z3.Expr.to_string phi))
    in
    let implicant = 
      match get_implicant false form with
      | Bot -> failwith "Unable to find implicant"
      | Ne i -> Ne i
    in
    local_project model projected_dims implicant
        


  let convex_hull ctx solver project_dims =
    let form = Z3.Boolean.mk_and ctx (Z3.Solver.get_assertions solver) in 
    Log.log_line_s ~level:`trace "Computing convex hull";
    let rec alpha_below polyhedron = 
      Log.log_line_s ~level:`trace "Current polyhedron";
      Log.log_line_s ~level:`trace (to_string "" polyhedron);
      match Z3.Solver.check solver [negate_poly ctx polyhedron] with
      | Z3.Solver.UNKNOWN -> failwith "Z3 returns with Unknown"
      | Z3.Solver.UNSATISFIABLE -> 
        vpl_poly_to_poly polyhedron
      | Z3.Solver.SATISFIABLE ->
        let model = match Z3.Solver.get_model solver with | None -> failwith "Unable to obtain model" | Some m -> m in
        let gen_poly = generalize_model model project_dims form in
        alpha_below (join polyhedron (poly_to_vpl_poly gen_poly))
    in
    alpha_below bottom
      
  let get_z3_consts form = 
    let rec aux phi seen_asts consts = 
      if BatISet.mem (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts then seen_asts, consts
      else
        if Z3.Expr.is_const phi && (not (Z3.Boolean.is_true phi || Z3.Boolean.is_false phi)) then 
          BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, BatISet.add ((Z3.Symbol.get_int % Z3.FuncDecl.get_name % Z3.Expr.get_func_decl) phi) consts
        else
          let children = Z3.Expr.get_args phi in
          if children = [] then BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, consts
          else
            let new_seen_asts, new_consts = List.fold_left (fun (pasts, pconsts) child -> aux child pasts pconsts) (seen_asts, consts) children in
            BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) new_seen_asts, new_consts
    in
    snd (aux form (BatISet.empty) (BatISet.empty))


  let find_cons ctx solver pot_cons (*biggest_flag_num*) = 
    Z3.Solver.push solver;
    let pot_cons_with_flags = List.mapi (fun i c -> (i, Z3.Boolean.mk_const_s ctx ("b" ^ (string_of_int (i(* + biggest_flag_num *)))), c)) pot_cons in
    (*let round_f = Z3.Boolean.mk_const_s ctx ("r" ^ (string_of_int biggest_flag_num)) in*)
    (*Z3.Solver.add solver [Z3.Boolean.mk_implies ctx round_f ( Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags))) ];*)
    Z3.Solver.add solver [Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags))];
    let rec aux cons_in_play cons_violated = 
      let assumpts = List.concat (List.map (fun (_, clist) -> List.map (fun (_, b, _) -> Z3.Boolean.mk_not ctx b) clist) cons_violated) in
      match Z3.Solver.check solver ((*round_f :: *)assumpts) with
      | Z3.Solver.UNKNOWN -> failwith "Error in z3 solver"
      | Z3.Solver.UNSATISFIABLE -> 
        Z3.Solver.pop solver 1;
        Z3.Solver.add solver (List.map (fun (_, _, c) -> c) cons_in_play);
        (*Z3.Solver.add solver [Z3.Boolean.mk_not ctx round_f];*)
        (List.map (fun (i, _, _) -> i) cons_in_play), (List.map (fun (m, clist) -> m, (List.map (fun (i, _, _) -> i) clist)) cons_violated)
      | Z3.Solver.SATISFIABLE ->
        (match Z3.Solver.get_model solver with
        | None -> failwith "Error getting model"
        | Some m ->
          let partitioner (_, _, con) = 
            let con_interp = match Z3.Model.eval m con true with | None -> failwith "Error getting interp" | Some e -> e in
            Z3.Boolean.is_true con_interp
          in
          let cs_still_in_play, cs_violated = List.partition partitioner cons_in_play in
          aux (List.rev cs_still_in_play) ((m, List.rev cs_violated) :: cons_violated)
        )
    in
    aux pot_cons_with_flags []



  let discover_eqs ctx solver poly = 
    match poly with
    | Bot -> Bot, []
    | Ne p ->
      let pot_eqs = p.non_strict in
      let (eqs, _) = find_cons ctx solver (List.map (cntsr_to_z3 `eq ctx) pot_eqs) in
      let new_eqs, still_ineqs, _ = 
        List.fold_left (
          fun (es, is, ind) cnstr -> 
            if List.mem ind eqs then (cnstr :: es, is, ind + 1) 
            else (es, cnstr :: is, ind + 1)) ([], [], 0) pot_eqs in
      Ne {p with eqs = p.eqs @ new_eqs; non_strict = List.rev still_ineqs}, eqs

  let find_new_constraints poly new_p = 
    match poly, new_p with
    | Bot, Bot -> [], [], []
    | Bot, Ne new_pp -> new_pp.eqs, new_pp.non_strict, new_pp.strict
    | Ne _, Bot -> failwith "Could add inconsistent constraint"
    | Ne pp, Ne new_pp ->
      let new_eqs = List.fold_left (
        fun es e -> if not (List.exists (lt_eq e) pp.eqs) then e :: es else es
      ) [] new_pp.eqs in
      let new_ineqs = List.fold_left (
        fun is i -> if not (List.exists (lt_eq i) pp.eqs) && not (List.exists (lt_eq i) pp.non_strict) then i :: is else is
      ) [] new_pp.non_strict in
      let new_strict = List.fold_left (
        fun ss s -> if not (List.exists (lt_eq s) pp.strict) then s :: ss else ss
      ) [] new_pp.strict in
      (new_eqs, new_ineqs, new_strict)



  let saturate ctx solver eqs non_strict strict form = 
    let poly = Ne {eqs; non_strict; strict} in
    let form_vars = get_z3_consts form in
    let poly_vars = get_poly_vars poly in
    let vars_to_project = BatISet.elements (BatISet.diff poly_vars form_vars) in
    Z3.Solver.push solver;
    Z3.Solver.add solver [form];
    let eq_poly, non_strict_to_upgrade = discover_eqs ctx solver poly in
    let hull = convex_hull ctx solver vars_to_project in
    let new_eqs, new_ineqs, new_strict = find_new_constraints eq_poly hull in
    if new_eqs <> [] then Log.log_line_s ~level:`trace "I thought this should always be empty";
    Z3.Solver.pop solver 1;
    let z3_new_eqs = List.map (cntsr_to_z3 `eq ctx) (List.map (List.nth non_strict) non_strict_to_upgrade) in
    let z3_new_ineqs = List.map (cntsr_to_z3 `ge ctx) new_ineqs in
    let z3_new_strict = List.map (cntsr_to_z3 `gt ctx) new_strict in
    Z3.Solver.add solver (z3_new_eqs @ z3_new_ineqs @ z3_new_strict);
    non_strict_to_upgrade, new_ineqs, new_strict
  
end