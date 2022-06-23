module Make (C : Sigs.Coefficient)(V : Sigs.Var) = struct

  let (%) = BatPervasives.(%)


  module DM = V.M
  
  type lterm = C.coef DM.map * C.coef

  let empty_m = DM.empty


  let pp_l f lt = 
    if DM.is_empty (fst lt) then (Format.pp_open_hbox f (); Format.pp_print_string f (C.to_string_c (snd lt)); Format.pp_close_box f ())
    else 
      let tlist = DM.fold 
        (fun dim coef l -> 
          if C.cmp coef C.zero < 0 then (C.to_string_c (C.mulc coef (C.from_string_c "-1")) ^ ".v" ^ (V.to_string dim), true) :: l
          else (C.to_string_c coef ^ ".v" ^ (V.to_string dim), false) :: l) (fst lt) [] in
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

  let lt_add a b = 
    let merger _ a_opt b_opt = 
      match a_opt, b_opt with
      | None, _ -> b_opt
      | _ , None -> a_opt
      | Some a_coef, Some b_coef ->
        let sum = C.addc a_coef b_coef in
        if C.cmp sum C.zero = 0 then None
        else Some sum
    in
    (*et folder adim acoef bmap = 
      if not (BatIMap.mem adim bmap) then BatIMap.add adim acoef bmap
      else
        let sum = C.addc acoef (BatIMap.find adim bmap) in
        if C.cmp sum C.zero = 0 then BatIMap.remove adim bmap
        else
          BatIMap.modify adim (fun _ -> sum) bmap
    in*)
    let new_map = DM.merge merger (fst a) (fst b) in
    let new_const = C.addc (snd a) (snd b) in
    (new_map, new_const)

  let lt_scalar_mult scalar t = 
    DM.map (C.mulc scalar) (fst t), C.mulc scalar (snd t)

  let lt_negate a = 
    lt_scalar_mult (C.from_string_c "-1") a
  
  

  let lt_cmp (am, ac) (bm, bc) = 
    let ccmp = C.cmp ac bc in
    if ccmp = 0 then
      DM.compare (C.cmp) am bm
    else ccmp

  let lt_replace v replace t = 
    let res = 
      if not (DM.mem v (fst t)) then t
      else
        let v_coef_in_t = DM.find v (fst t) in
        if C.cmp v_coef_in_t C.zero = 0 then (DM.remove v (fst t), snd t)
        else
          let res_with_v = lt_add t (lt_scalar_mult v_coef_in_t replace) in
          DM.remove v (fst res_with_v), snd res_with_v
    in
    (*if lt_eq res problem_term then (Log.log_s ~level:`trace ("v" ^ (string_of_int v) ^ " -> "); Log.log ~level:`trace pp_l (Some replace); Log.log ~level:`trace pp_l (Some t));*)
    res

  let lt_eval m (map, const) = 
    let folder dim coef (res_map, res_const) = 
      if not (DM.mem dim m) then DM.add dim coef res_map, res_const
      else
        let v = C.mulc coef (DM.find dim m) in
        (res_map, C.addc v res_const)
    in
    DM.fold folder map (empty_m, const)

  module S = BatSet.Make(struct type t = lterm let compare = lt_cmp end)

  (*type ne_poly = {eqs: lterm list; non_strict: lterm list; strict: lterm list}*)

  type ne_poly = {eqs: S.t; non_strict: S.t; strict: S.t}

  type polyhedron = | Bot | Ne of ne_poly

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
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_eq f (S.to_list cnstrs.eqs);
      Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_ge f (S.to_list cnstrs.non_strict);
      Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_gt f (S.to_list cnstrs.strict);
      Format.pp_close_box f ()

  let add_cnstr kind poly (c_map, const) = 
    match poly with
    | Bot -> Bot
    | Ne p ->
      (match kind with
      | `eq ->
        if DM.is_empty c_map && C.cmp const C.zero <> 0 then Bot
        else if DM.is_empty c_map then poly
        else Ne {p with eqs = S.add (c_map, const) p.eqs}
      | `ge ->
        if DM.is_empty c_map && C.cmp const C.zero < 0 then Bot
        else if DM.is_empty c_map then poly
        else Ne {p with non_strict = S.add (c_map, const) p.non_strict}
      | `gt ->
        if DM.is_empty c_map && C.cmp const C.zero <= 0 then Bot
        else if DM.is_empty c_map then poly
        else Ne {p with strict = S.add (c_map, const) p.strict}
      )

  let meet x y = 
    match x, y with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Ne px, Ne py ->
      Ne {eqs = S.union px.eqs py.eqs; non_strict = S.union px.non_strict py.non_strict; strict = S.union px.strict py.strict}
      (*let comb_eqs = List.fold_left (add_cnstr `eq) y p.eqs in
      let comb_eqs_and_ns = List.fold_left (add_cnstr `ge) comb_eqs p.non_strict in
      List.fold_left (add_cnstr `gt) comb_eqs_and_ns p.strict*)

  let top_p = Ne {eqs = S.empty; non_strict = S.empty; strict = S.empty}

  let replace v replace poly = 
    match poly with
    | Bot -> Bot
    | Ne p ->
      Ne {eqs = S.map (lt_replace v replace) p.eqs; non_strict = S.map (lt_replace v replace) p.non_strict; strict = S.map (lt_replace v replace) p.strict}

      (*let folder kind res p_term = add_cnstr kind res (lt_replace v replace p_term) in
      List.fold_left (folder `eq) (List.fold_left (folder `ge) (List.fold_left (folder `gt) top_p p.strict) p.non_strict) p.eqs*)

  module A = struct

    open Apron.Lincons1

    let man = Polka.manager_alloc_strict ()

    type t = Polka.strict Polka.t Apron.Abstract1.t

    let bottom env = Apron.Abstract1.bottom man env

    let var_to_apron_var d = Apron.Var.of_string (V.to_string d)

    let var_to_dim v = Apron.Var.to_string v 

    let var_list_to_env dim_list = Apron.Environment.make [||] (Array.of_list (List.map (Apron.Var.of_string % V.to_string) dim_list))

    let of_poly env poly : t = 
      match poly with
      | Bot -> Apron.Abstract1.bottom man env
      | Ne poly ->
        let lterm_to_lincons typ (map, const) = 
          let coef_list = DM.fold (fun dim coef l -> (Apron.Coeff.s_of_mpq (Mpq.of_string (C.to_string_c coef)), var_to_apron_var dim) :: l) map [] in
          let a_const = (*if C.cmp const C.zero = 0 then None else*) Some (Apron.Coeff.s_of_mpq (Mpq.of_string (C.to_string_c const))) in
          let expr = Apron.Linexpr1.make env in
          Apron.Linexpr1.set_list expr coef_list a_const;
          match typ with
          | `eq -> (make expr EQ)
          | `ge -> (make expr SUPEQ)
          | `gt -> (make expr SUP)
        in
        let cnstrs = List.map (lterm_to_lincons `eq) (S.to_list poly.eqs) @ List.map (lterm_to_lincons `ge) (S.to_list poly.non_strict) @ List.map (lterm_to_lincons `gt) (S.to_list poly.strict) in
        (*List.iter (fun c ->
          Log.log ~level:`trace (Apron.Lincons1.print (fun i -> "v." ^ (string_of_int i))) (Some c)
        ) cnstrs;*)
        let earr = Apron.Lincons1.array_make env (List.length cnstrs) in
        List.iteri (fun i c -> Apron.Lincons1.array_set earr i c) cnstrs;
        Apron.Abstract1.of_lincons_array man env earr

    let to_poly (polyhedron : t) = 
      if Apron.Abstract1.is_bottom man polyhedron then Bot 
      else
        let coef_to_c c = 
          match c with
            | Apron.Coeff.Scalar s -> 
              C.from_string_c (Apron.Scalar.to_string s)
            | _ -> failwith "Expr has interval coef"
          in
        let linexpr_to_map le = 
          let map = ref (empty_m) in
          let iterator c v = 
            if C.cmp (coef_to_c c) C.zero <> 0 then
              let dim = V.of_string (var_to_dim v) in
              map := DM.add dim (coef_to_c c) !map 
          in
          Apron.Linexpr1.iter iterator le;
          let const = coef_to_c (Apron.Linexpr1.get_cst le) in
          !map, const
        in
        let folder poly cnstr = 
          match get_typ cnstr with
          | EQ -> add_cnstr `eq poly (linexpr_to_map (get_linexpr1 cnstr))
          | SUPEQ -> add_cnstr `ge poly (linexpr_to_map (get_linexpr1 cnstr))
          | SUP -> add_cnstr `gt poly (linexpr_to_map (get_linexpr1 cnstr))
          | _ -> failwith "Diseq or eqmod constraint in apron poly"
        in
        let earr = Apron.Abstract1.to_lincons_array man polyhedron in
        let lincons1arr = Array.map (fun lincons0 -> {lincons0; env = earr.array_env}) earr.lincons0_array in
        Array.fold_left folder top_p lincons1arr

    let join a b = 
      (*Log.log ~level:`trace (Apron.Abstract0.print (fun i -> "v." ^ (string_of_int i))) (Some a);
      Log.log ~level:`trace (Apron.Abstract0.print (fun i -> "v." ^ (string_of_int i))) (Some b);*)
      Apron.Abstract1.join man a b

  end


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

  let cntsr_to_z3 kind ctx c =
    let term_to_z3 dim coef = 
      Z3.Arithmetic.mk_mul ctx [Z3.Arithmetic.Real.mk_numeral_s ctx (C.to_string_c coef); Z3.Arithmetic.Real.mk_const ctx (Z3.Symbol.mk_int ctx (V.hash dim))]
    in
    let lhs = Z3.Arithmetic.mk_add ctx (DM.fold (fun dim coef acc -> (term_to_z3 dim coef) :: acc) (fst c) [Z3.Arithmetic.Real.mk_numeral_s ctx (C.to_string_c (snd c))]) in
    match kind with
    | `eq -> Z3.Boolean.mk_eq ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
    | `ge -> Z3.Arithmetic.mk_ge ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)
    | `gt -> Z3.Arithmetic.mk_gt ctx lhs (Z3.Arithmetic.Real.mk_numeral_i ctx 0)


  let poly_to_z3 ctx polyhedron = 
    match polyhedron with
    | Bot -> Z3.Boolean.mk_false ctx
    | Ne p ->
      let z3eqs = List.map (cntsr_to_z3 `eq ctx) (S.to_list p.eqs) in
      let z3non_strict = List.map (cntsr_to_z3 `ge ctx) (S.to_list p.non_strict) in
      let z3strict = List.map (cntsr_to_z3 `gt ctx) (S.to_list p.strict) in
      let cnstrs = z3eqs @ z3non_strict @ z3strict in
      if cnstrs = [] then Z3.Boolean.mk_true ctx
      else Z3.Boolean.mk_and ctx cnstrs

       
  (*let z3_atom_to_poly negate phi = 
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
    *)



  (*let get_poly_vars p = 
    match p with
    | Bot -> V.S.empty
    | Ne poly ->
      let folder cnstr set = V.S.union (DM.domain (fst cnstr)) set in
      S.fold folder poly.eqs (S.fold folder poly.non_strict (S.fold folder poly.strict V.S.empty)) *)

  let z3_atom_to_polyhedron negate phi = 
    let rec z3_term_to_lterm t = 
      if Z3.Expr.is_const t then
        let name = Z3.FuncDecl.get_name (Z3.Expr.get_func_decl t) in
        let v = if Z3.Symbol.is_int_symbol name then V.of_int (Z3.Symbol.get_int name)
                else V.of_string (Z3.Symbol.get_string name)
                in
        (DM.add v C.one (empty_m), C.zero)
      else if Z3.Arithmetic.is_rat_numeral t then
        (empty_m, C.of_zarith_q (Z3.Arithmetic.Real.get_ratio t))
      else if Z3.Arithmetic.is_mul t then
        let (const, var) = List.partition (fun e -> Z3.Arithmetic.is_rat_numeral e) (Z3.Expr.get_args t) in
        if List.length var > 1 then failwith ("Non-linear formula: " ^ (Z3.Expr.to_string t))
        else 
          let const_term = List.fold_left (fun acc e -> C.mulc (C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)) acc) C.one const in
          if var = [] then (empty_m, const_term)
          else
            let name = Z3.FuncDecl.get_name (Z3.Expr.get_func_decl (List.hd var)) in
            let v = if Z3.Symbol.is_int_symbol name then V.of_int (Z3.Symbol.get_int name)
                else V.of_string (Z3.Symbol.get_string name)
                in
            (DM.add v const_term (empty_m), C.zero)
      else if Z3.Arithmetic.is_add t then
        let sub_terms = List.map z3_term_to_lterm (Z3.Expr.get_args t) in
        List.fold_left lt_add (List.hd sub_terms) (List.tl sub_terms)
      else
        failwith ("Unknown z3 term: " ^ (Z3.Expr.to_string t))
    in
    let lhs = z3_term_to_lterm (List.nth (Z3.Expr.get_args phi) 0) in
    let rhs = z3_term_to_lterm (List.nth (Z3.Expr.get_args phi) 1) in
    if ((not negate) && (Z3.Arithmetic.is_ge phi || Z3.Arithmetic.is_gt phi)) || (negate && (Z3.Arithmetic.is_le phi || Z3.Arithmetic.is_lt phi)) then (* lhs >= rhs || lhs > rhs || not (lhs < rhs) || not (lhs <= rhs)*)
      let lhs_minus_rhs = lt_add lhs (lt_negate rhs) in
      if Z3.Arithmetic.is_ge phi || (negate && Z3.Arithmetic.is_lt phi) then (* lhs >= rhs || not (lhs < rhs) *)
        add_cnstr `ge top_p lhs_minus_rhs
      else 
        add_cnstr `gt top_p lhs_minus_rhs (* lhs > rhs || not (lhs <= rhs) *)
    else if negate && Z3.Boolean.is_eq phi then (* lhs <> rhs *)
      let lhs_minus_rhs = lt_add lhs (lt_negate rhs) in (* lhs - rhs > 0 *)
      let rhs_minus_lhs = lt_add rhs (lt_negate lhs) in (* rhs - lhs > 0 *)
      add_cnstr `gt (add_cnstr `gt top_p lhs_minus_rhs) rhs_minus_lhs
    else if Z3.Boolean.is_eq phi then add_cnstr `eq top_p (lt_add lhs (lt_negate rhs))
    else (* lhs <= rhs || lhs < rhs || not (lhs > rhs) || not (lhs >= rhs)*)
      let rhs_minus_lhs = lt_add rhs (lt_negate lhs) in
      if Z3.Arithmetic.is_le phi || (negate && Z3.Arithmetic.is_gt phi) then add_cnstr `ge top_p rhs_minus_lhs
      else if Z3.Arithmetic.is_lt phi || (negate && Z3.Arithmetic.is_ge phi) then add_cnstr `gt top_p rhs_minus_lhs
      else failwith "All cases should have been covered"



  type vt = | MinusInf | Term of (C.coef DM.map * C.coef) | TermEp of (C.coef DM.map * C.coef)


  (*let pp_cm f cm = 
    let cm_list = DM.fold (fun dim c l -> (("v" ^ (string_of_int dim)), C.to_string_c c) :: l) cm [] in
    let print_p fo (v, c) = 
      Format.pp_open_hbox fo (); Format.pp_print_string fo (v ^ " -> " ^ c); Format.pp_close_box fo ()
    in
    Format.pp_open_vbox f 0;
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) print_p f cm_list

  *)

  let project_dim m polyhedron d = 
    (*Log.log_line_s ("Projecting " ^ ( string_of_int d) ^ ":"); Log.log ~level:`trace pp_52 (Some polyhedron);*)
    (*if d = 51 then (Log.log_line_s "Projecting 51:"; Log.log ~level:`trace pp_52 (Some polyhedron));
    if d = 52 then (Log.log_line_s "Projecting 52:"; Log.log ~level:`trace pp_52 (Some polyhedron));*)
    match polyhedron with | Bot -> Bot | Ne p ->
    let vt = 
      let merge_vt x y = (* pick the biggest lower bound favoring strict lower bounds. None is minus infinity. *)
        match x, y with
        | None, _ -> y
        | _, None -> x
        | Some (_, value, _), Some (_, value', _) when C.cmp value value' < 0 -> y
        | Some (_, value, _), Some (_, value', _) when C.cmp value value' > 0 -> x
        | Some (_, _, _), Some (_, _, true) -> y
        | _ -> x
      in
      let search_eq_terms (map, const) found = 
        match found with
        | Some _ -> found
        | None -> 
          if DM.mem d map then
            let d_coef = DM.find d map in
            if C.cmp d_coef C.zero = 0 then None
            else (* ad + b = 0 && a <> 0 => d = -b/a *)
              let mul = C.divc (C.from_string_c "-1") d_coef in (* -1/a *)
              let eq_term = lt_scalar_mult mul (DM.remove d map, const) in
              Some (eq_term)
          else None
      in
      match S.fold search_eq_terms p.eqs None with
      | Some t -> Term t
      | None ->
        let folder is_strict (vmap, const) vt = 
          let d_coef = try DM.find d vmap with Not_found -> C.zero in
          if C.cmp d_coef C.zero <= 0 then vt
          else (* (ad + b >=0 || ad + b > 0) && a > 0 => d >= -b/d || d > -b/d *)
            let lower_b = lt_scalar_mult (C.divc (C.from_string_c "-1") d_coef) (DM.remove d vmap, const) in (* -b/d *)
            let (lower_b_m, lower_b_interp) = lt_eval m lower_b in
            if not (DM.is_empty lower_b_m) then failwith "Model wasn't complete for evaluating lower bounds";
            merge_vt vt (Some (lower_b, lower_b_interp, is_strict))
        in
        match S.fold (folder true) p.strict (S.fold (folder false) p.non_strict None) with
        | None -> MinusInf
        | Some (t, _, false) -> Term t
        | Some (t, _, true) -> TermEp t
    in
    match vt with
    | Term t -> replace d t polyhedron
    | MinusInf -> 
      let fold_eqs (c_map, const) poly = 
        if not (DM.mem d c_map) then add_cnstr `eq poly (c_map, const) (* This is the only case that should happen. Everything else is sanity checks*)
        else if C.cmp (DM.find d c_map) C.zero = 0 then add_cnstr `eq poly (DM.remove d c_map, const)
        else Bot
      in
      let fold_ineqs strict (c_map, const) poly = 
        if not (DM.mem d c_map) || C.cmp (DM.find d c_map) C.zero = 0 then 
          let rem_map = if (DM.mem d c_map) && C.cmp (DM.find d c_map) C.zero = 0 then DM.remove d c_map else c_map in
          (if strict then add_cnstr `gt poly (rem_map, const)
          else add_cnstr `ge poly (rem_map, const))
        else 
          (if C.cmp (DM.find d c_map) C.zero > 0 then Bot
          else poly) (* This is is the only case that should happen. Everything else is sanity checks*)
      in
      S.fold fold_eqs p.eqs (S.fold (fold_ineqs false) p.non_strict(S.fold (fold_ineqs true) p.strict top_p))
    | TermEp t -> 
      let fold_eqs (c_map, const) poly =
        if not (DM.mem d c_map) then add_cnstr `eq poly (c_map, const) (* This is the only case that should happen. Everything else is sanity checks*)
        else if C.cmp (DM.find d c_map) C.zero = 0 then add_cnstr `eq poly (DM.remove d c_map, const)
        else Bot 
      in
      let fold_ineqs strict (c_map, const) poly = 
        if (not (DM.mem d c_map)) && strict then add_cnstr `gt poly (c_map, const)
        else if not (DM.mem d c_map) then add_cnstr `ge poly (c_map, const)
        else
          let d_coef = DM.find d c_map in
          if C.cmp d_coef C.zero = 0 && strict then add_cnstr `gt poly (DM.remove d c_map, const)
          else if C.cmp d_coef C.zero = 0 then add_cnstr `ge poly (DM.remove d c_map, const)
          else 
            let new_c = lt_replace d t (c_map, const) in
            if C.cmp C.zero d_coef < 0 then add_cnstr `ge poly new_c
            else add_cnstr `gt poly new_c
      in
      S.fold fold_eqs p.eqs (S.fold (fold_ineqs false) p.non_strict (S.fold (fold_ineqs true) p.strict top_p))
          
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


  let z3_model_to_dm model = 
    List.fold_left (fun map fun_decl -> 
          if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then map (* Not a general solution *)
          else
            let interp = match Z3.Model.get_const_interp model fun_decl with
              | None -> failwith "Const has no interpretation in model"
              | Some e -> C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
            in
            let name = Z3.FuncDecl.get_name fun_decl in
            let v = if Z3.Symbol.is_int_symbol name then V.of_int (Z3.Symbol.get_int name)
                else V.of_string (Z3.Symbol.get_string name)
                in
            DM.add v interp map) (empty_m) (Z3.Model.get_const_decls model)


  (*let local_project model project_dims p =
    List.fold_left (project_dim (z3_model_to_dm model)) p project_dims*)


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
  

  let generalize_model model form = 
    let models_sats neg formula = 
      let t_interp = 
        match Z3.Model.eval model formula false with
       | None -> failwith "Error evaluating model"
       | Some e -> Z3.Boolean.is_true e
      in
      if neg then not t_interp
      else t_interp
    in
    let rec get_implicant negate phi = 
      if not (models_sats negate phi) then Bot
      else (* phi has a satisfied disjunct and is to be explored *)
        if Z3.Boolean.is_and phi then
          let get_and_check_child_impls processed_children child = 
            match processed_children with
            | Bot -> Bot
            | Ne _ -> meet processed_children (get_implicant negate child)
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
          let head, tail = List.nth (Z3.Expr.get_args phi) 0, List.nth (Z3.Expr.get_args phi) 1 in
          match get_implicant negate tail with
          | Ne cs -> Ne cs
          | Bot -> get_implicant (not negate) head
        else if Z3.Arithmetic.is_ge phi || Z3.Arithmetic.is_gt phi || Z3.Arithmetic.is_le phi || Z3.Arithmetic.is_lt phi || Z3.Boolean.is_eq phi then
          z3_atom_to_polyhedron negate phi
        else failwith ("Unknown formula node: " ^ (Z3.Expr.to_string phi))
      in
    match get_implicant false form with
    | Bot -> failwith "Unable to find implicant"
    | Ne i -> Ne i

        
      
  let get_z3_consts form = 
    let rec aux phi seen_asts consts = 
      if BatSet.mem (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts then seen_asts, consts
      else
        if Z3.Expr.is_const phi && (not (Z3.Boolean.is_true phi || Z3.Boolean.is_false phi)) then 
          let name = Z3.FuncDecl.get_name (Z3.Expr.get_func_decl phi) in
          let v = if Z3.Symbol.is_int_symbol name then V.of_int (Z3.Symbol.get_int name)
                else V.of_string (Z3.Symbol.get_string name)
                in
          BatSet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, V.S.add v consts
        else
          let children = Z3.Expr.get_args phi in
          if children = [] then BatSet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, consts
          else
            let new_seen_asts, new_consts = List.fold_left (fun (pasts, pconsts) child -> aux child pasts pconsts) (seen_asts, consts) children in
            BatSet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) new_seen_asts, new_consts
    in
    snd (aux form (BatSet.empty) (V.S.empty))

  let convex_hull ctx solver =
    let form = Z3.Boolean.mk_and ctx (Z3.Solver.get_assertions solver) in
    let form_vars = get_z3_consts form in
    (*let hull_set = List.fold_left (fun s d -> BatSet.remove d s) (get_z3_consts form) project_dims in
    let hull_vars = BatSet.elements hull_set in*)
    let env = A.var_list_to_env (V.S.to_list form_vars) in
    (*let quantified_form = project_vars ctx form (List.map (Z3.Symbol.mk_int ctx) project_dims) in
    let tmp_solver = Z3.Solver.mk_simple_solver ctx in
    Z3.Solver.add tmp_solver [quantified_form];
    Log.log_line_s ~level:`trace (Z3.Solver.to_string tmp_solver);*)
    Z3.Solver.push solver;
    let rec alpha_below polyhedron = 
      let p = A.to_poly polyhedron in
      Log.log_line_s ~level:`trace "Curr poly:";
      Log.log ~level:`trace pp (Some p);
      let z3p = poly_to_z3 ctx p in
      Z3.Solver.add solver [Z3.Boolean.mk_not ctx z3p];
      (match Z3.Solver.check solver [] with
      | Z3.Solver.UNKNOWN -> failwith "Z3 returns with Unknown"
      | Z3.Solver.UNSATISFIABLE -> 
        (Z3.Solver.pop solver 1;
        p)
      | Z3.Solver.SATISFIABLE ->
        (let model = (match Z3.Solver.get_model solver with | None -> failwith "Unable to obtain model" | Some m -> m) in
        let implicant = generalize_model model form in
        let apron = A.of_poly env implicant in
        let next = A.join polyhedron apron in

        (*(let m_proj = 
        List.fold_left (fun map fun_decl -> 
          if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then map (* Not a general solution *)
          else
            let interp = match Z3.Model.get_const_interp model fun_decl with
            | None -> failwith "Const has no interpretation in model"
            | Some e-> 
              C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
            in
            let dim = Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl) in
            if BatISet.mem dim hull_set then BatIMap.add dim interp map 
            else map) (empty_m) (Z3.Model.get_const_decls model)
            in


        (*Log.log_line_s ~level:`trace "Implicant with 13 or 14: ";
        Log.log ~level:`trace pp_52 (Some implicant);*)

        (*let tmp_solver = Z3.Solver.mk_simple_solver ctx in
        Z3.Solver.add tmp_solver [poly_to_z3 ctx implicant];*)
        (*Log.log_line_s ~level:`trace "Z3 implicant";
        Log.log_line_s ~level:`trace (Z3.Expr.to_string (poly_to_z3 ctx implicant));*)

        Log.log_line_s ~level:`trace "Projected model: ";
        Log.log ~level:`trace pp_cm (Some m_proj);

        Log.log_line_s ~level:`trace "Projected poly: ";
        Log.log ~level:`trace pp (Some proj_poly);

        Log.log_line_s ~level:`trace "Implicant: ";
        Log.log ~level:`trace pp (Some implicant);

        Log.log_line_s ~level:`trace "Projected poly apron: ";
        Log.log ~level:`trace Apron.Abstract1.print (Some apron));
        
        
        let next_z3 = poly_to_z3 ctx (A.to_poly next) in
        ((match Z3.Model.eval model next_z3 false with
        | None -> failwith "Couldn't eval model"
        | Some e -> 
          if not (Z3.Boolean.is_true e) then Log.log_line_s ~level:`trace "Model doesn't sat next polyhedron");
        (match Z3.Model.eval model (poly_to_z3 ctx proj_poly) false with
        | None -> failwith "Couldn't eval model"
        | Some e -> 
          if not (Z3.Boolean.is_true e) then Log.log_line_s ~level:`trace "Model doesn't sat proj_poly");
        (match Z3.Model.eval model (poly_to_z3 ctx implicant) false with
          | None -> failwith "Couldn't eval model"
          | Some e -> 
          if not (Z3.Boolean.is_true e) then Log.log_line_s ~level:`trace "Model doesn't sat implicant");
        (match Z3.Model.eval model z3p false with
        | None -> failwith "Couldn't eval model"
        | Some e -> 
          if (Z3.Boolean.is_true e) then Log.log_line_s ~level:`trace "Model sats prev polyhedron"));

        let nctx = Z3.mk_context [] in
        let tmp_solver = Z3.Solver.mk_simple_solver nctx in
        (match Z3.Solver.check tmp_solver [poly_to_z3 nctx proj_poly] with
        | Z3.Solver.UNKNOWN | Z3.Solver.SATISFIABLE -> ()
        | Z3.Solver.UNSATISFIABLE -> 
          Log.log_line_s ~level:`trace "Projected poly isn't SAT!");
        (* check model |= next, model |= gen_poly, gen_poly |= next, polyhedron |= next, model |= not polyhedron*) *)

        Log.log_line_s ~level:`trace "Join Complete";
        alpha_below next))
    in
    alpha_below (A.bottom env)


  let find_cons ?(use_flags=true) ctx solver pot_cons (*biggest_flag_num*) = 
    Z3.Solver.push solver;
    let pot_cons_with_flags = List.mapi (fun i c -> (i, Z3.Boolean.mk_const_s ctx ("b" ^ (string_of_int (i(* + biggest_flag_num *)))), c)) pot_cons in
    (*let round_f = Z3.Boolean.mk_const_s ctx ("r" ^ (string_of_int biggest_flag_num)) in*)
    (*Z3.Solver.add solver [Z3.Boolean.mk_implies ctx round_f ( Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags))) ];*)
    if use_flags then  Z3.Solver.add solver [Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags))];
    let rec aux cons_in_play cons_violated = 
      let assumpts = 
        if use_flags then List.concat (List.map (fun (_, clist) -> List.map (fun (_, b, _) -> Z3.Boolean.mk_not ctx b) clist) cons_violated) 
        else
          [Z3.Boolean.mk_or ctx (List.map (fun (_, _, c) -> Z3.Boolean.mk_not ctx c) cons_in_play)]
        in
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



  let discover_eqs ctx solver poly pot_eqs = 
    let (eqs, _) = find_cons ctx solver (List.map (cntsr_to_z3 `eq ctx) pot_eqs) in
    let new_eqs, still_ineqs, _ = 
       List.fold_left (
        fun (es, is, ind) cnstr -> 
          if List.mem ind eqs then (cnstr :: es, is, ind + 1) 
          else (es, cnstr :: is, ind + 1)) ([], [], 0) pot_eqs in
    let poly_plus_eqs = List.fold_left (add_cnstr `eq) poly new_eqs in
    match poly_plus_eqs with | Bot -> Bot, eqs | Ne x -> Ne {x with non_strict = S.of_list still_ineqs}, eqs

  let find_new_constraints poly new_p = 
    match poly, new_p with
    | Bot, Bot -> [], [], []
    | Bot, Ne new_pp -> S.to_list new_pp.eqs, S.to_list new_pp.non_strict, S.to_list new_pp.strict
    | Ne _, Bot -> failwith "Could add inconsistent constraint"
    | Ne pp, Ne new_pp ->
      (*let folder mem_list found lt = 
        if List.exists (lt_eq lt) mem_list then found
        else lt :: found
      in
      List.fold_left (folder pp.eqs) [] new_pp.eqs, List.fold_left (folder pp.non_strict) [] new_pp.non_strict, List.fold_left (folder pp.strict) [] new_pp.strict*)
      S.to_list (S.diff new_pp.eqs pp.eqs), S.to_list (S.diff new_pp.non_strict pp.non_strict), S.to_list (S.diff new_pp.strict pp.strict)



  let saturate ctx solver eqs non_strict strict form =
    (*Log.log_line_s ~level:`trace "Saturate w.r.t formula:";
    Log.log_line_s ~level:`trace (Z3.Expr.to_string form);
    Log.log_line_s ~level:`trace "";
    Log.log_line_s ~level:`trace "And Solver";
    Log.log_line_s ~level:`trace (Z3.Solver.to_string solver);
    Log.log_line_s ~level:`trace "";*)

    let poly = Ne {eqs = S.of_list eqs; non_strict = S.of_list non_strict; strict = S.of_list strict} in
    (*let form_vars = get_z3_consts form in
    let poly_vars = get_poly_vars poly in
    let vars_to_project = BatSet.elements (BatSet.diff poly_vars form_vars) in*)
    Z3.Solver.push solver;
    Z3.Solver.add solver [form];
    let eq_poly, non_strict_to_upgrade = discover_eqs ctx solver poly non_strict in
    Log.log_line_s ~level:`trace ("Extracted equations");
    let hull = convex_hull ctx solver in

    Log.log_line_s ~level:`trace "Computed convex hull:";
    Log.log ~level:`trace pp (Some hull);

    let new_eqs, new_ineqs, new_strict = find_new_constraints eq_poly hull in
    if new_eqs <> [] then Log.log_line_s ~level:`trace "I thought this should always be empty";
    Z3.Solver.pop solver 1;
    let z3_new_eqs = List.map (cntsr_to_z3 `eq ctx) (List.map (List.nth non_strict) non_strict_to_upgrade) in
    let z3_new_ineqs = List.map (cntsr_to_z3 `ge ctx) new_ineqs in
    let z3_new_strict = List.map (cntsr_to_z3 `gt ctx) new_strict in (* not sure about this *)
    Z3.Solver.add solver (z3_new_eqs @ z3_new_ineqs @ z3_new_strict);
    non_strict_to_upgrade, new_ineqs, new_strict


  let discover_eqs_ineqs ctx solver poly pot_eqs pot_ineqs = 
    let pot_cons = List.map (cntsr_to_z3 `eq ctx) pot_eqs @ List.map (cntsr_to_z3 `ge ctx) pot_ineqs in
    let (cons, _) = find_cons ctx solver pot_cons in
    let new_eqs, new_poly, _ = 
       List.fold_left (
        fun (es, p, ind) cnstr -> 
          if List.mem ind cons && ind < List.length pot_eqs then
            let temp_p = add_cnstr `eq p cnstr in
            match temp_p with
            | Bot -> ind :: es, Bot, ind + 1
            | Ne pp -> ind :: es, Ne {pp with non_strict = S.remove cnstr pp.non_strict}, ind+1
          else if List.mem ind cons then
            es, add_cnstr `ge p cnstr, ind+1
          else es, p, ind + 1) ([], poly, 0) (pot_eqs @ pot_ineqs) in
    new_poly, new_eqs


  let saturate_c ctx solver eqs non_strict strict form ineqs_to_check =
    (*Log.log_line_s ~level:`trace "Saturate w.r.t formula:";
    Log.log_line_s ~level:`trace (Z3.Expr.to_string form);
    Log.log_line_s ~level:`trace "";
    Log.log_line_s ~level:`trace "And Solver";
    Log.log_line_s ~level:`trace (Z3.Solver.to_string solver);
    Log.log_line_s ~level:`trace "";*)

    let poly = Ne {eqs = S.of_list eqs; non_strict = S.of_list non_strict; strict = S.of_list strict} in
    Z3.Solver.push solver;
    Z3.Solver.add solver [form];
    let eq_poly, non_strict_to_upgrade = discover_eqs_ineqs ctx solver poly non_strict ineqs_to_check in

    let _, new_ineqs, new_strict = find_new_constraints poly eq_poly in
    Z3.Solver.pop solver 1;
    let z3_new_eqs = List.map (cntsr_to_z3 `eq ctx) (List.map (List.nth non_strict) non_strict_to_upgrade) in
    let z3_new_ineqs = List.map (cntsr_to_z3 `ge ctx) new_ineqs in
    let z3_new_strict = List.map (cntsr_to_z3 `gt ctx) new_strict in (* not sure about this *)
    Z3.Solver.add solver (z3_new_eqs @ z3_new_ineqs @ z3_new_strict);
    non_strict_to_upgrade, new_ineqs, new_strict
  

  type bound = NoBound | Upper of polyhedron | Lower of polyhedron | Both of polyhedron

  (*let is_bound kind dim (c_map, _) = 
    if not (DM.mem dim c_map) then NoBound
    else
      let dim_coef = DM.find dim c_map in
      if C.cmp dim_coef C.zero = 0 then NoBound
      else
        let is_lower = C.cmp dim_coef C.zero > 0 in
        match kind with
        | `eq -> Both
        | `ge | `gt when is_lower -> Lower
        | `ge | `gt -> Upper

  let has_bound dim poly = 
    match poly with
    | Bot -> failwith "Trying to bound dim w.r.t empty bound"
    | Ne p ->
      let merge_bounds a b = 
        match a, b with
        | Both, _ -> Both
        | _, Both -> Both
        | Upper, Lower -> Both
        | Lower, Upper -> Both
        | NoBound, _ -> b
        | _, NoBound -> a
        | _ -> a
      in
      let find_bound kind (c_map, _) bound = 
        match bound with
        | Both -> bound
        | _ -> merge_bounds bound (is_bound kind dim (c_map, 0))
      in
      S.fold (find_bound `eq) p.eqs (S.fold (find_bound `ge) p.non_strict (S.fold (find_bound `gt) p.strict NoBound))*)
      

  let collect_bounds dim poly = 
    match poly with
    | Bot -> failwith "Trying to bound dim w.r.t empty bound"
    | Ne p ->
      let folder kind (c_map, const) b_poly = 
        if not (DM.mem dim c_map) || C.cmp (DM.find dim c_map) C.zero = 0 then b_poly
        else
          match b_poly with
          | NoBound ->
            (match kind with
            | `eq -> Both (add_cnstr kind top_p (c_map, const))
            | `ge | `gt ->
              if C.cmp (DM.find dim c_map) C.zero < 0 then Upper (add_cnstr kind top_p (c_map, const))
              else Lower (add_cnstr kind top_p (c_map, const))
            )
          | Both b -> Both (add_cnstr kind b (c_map, const))
          | Upper b ->
            if C.cmp (DM.find dim c_map) C.zero < 0 then Upper (add_cnstr kind b (c_map, const))
            else Both (add_cnstr kind b (c_map, const))
          | Lower b ->
            if C.cmp (DM.find dim c_map) C.zero < 0 then Both (add_cnstr kind b (c_map, const))
            else Lower (add_cnstr kind b (c_map, const))
      in
      S.fold (folder `eq) p.eqs (S.fold (folder `ge) p.non_strict (S.fold (folder `gt) p.strict NoBound))






        (*match is_bound kind dim (c_map, const) with
        | NoBound -> uppers, lowers
        | Both ->
          let bound = lt_scalar_mult (C.divc (C.from_string_c "-1") (DM.find dim c_map)) (DM.remove dim c_map, const) in
          let new_uppers = S.add bound uppers (*if List.exists (lt_eq bound) uppers then uppers else bound :: uppers *)in
          let new_lowers = S.add bound lowers (*if List.exists (lt_eq bound) lowers then lowers else bound :: lowers *)in
          (new_uppers, new_lowers)
        | Upper ->
          let bound = lt_scalar_mult (C.divc (C.from_string_c "-1") (DM.find dim c_map)) (DM.remove dim c_map, const) in
          let new_uppers = S.add bound uppers (*if List.exists (lt_eq bound) uppers then uppers else bound :: uppers*) in
          (new_uppers, lowers)
        | Lower ->
          let bound = lt_scalar_mult (C.divc (C.from_string_c "-1") (DM.find dim c_map)) (DM.remove dim c_map, const) in
          let new_lowers = S.add bound lowers (*if List.exists (lt_eq bound) lowers then lowers else bound :: lowers *)in
          (uppers, new_lowers)
      in
      S.fold (folder `eq) p.eqs (S.fold (folder `ge) p.non_strict (S.fold (folder `gt) p.strict (S.empty, S.empty)))*)
  
  let extract_bounds dim p =
    match p with
    | Bot -> failwith "An empty polyhedron can't bound anything"
    | Ne bounding_p ->
      let folder kind (cmap, const) (uppers, lowers) = 
        if not (DM.mem dim cmap) || C.cmp (DM.find dim cmap) C.zero = 0 then (uppers, lowers)
        else
          let dim_coef = DM.find dim cmap in
          let bound = lt_scalar_mult (C.divc (C.from_string_c "-1") dim_coef) (DM.remove dim cmap, const) in
          match kind with
          | `eq -> (S.add bound uppers, S.add bound lowers)
          | `ge | `gt ->
            if C.cmp dim_coef C.zero < 0 then (S.add bound uppers, lowers)
            else (uppers, S.add bound lowers)
      in
      S.fold (folder `eq) bounding_p.eqs (S.fold (folder `ge) bounding_p.non_strict (S.fold (folder `gt) bounding_p.strict (S.empty, S.empty)))

  let check_bounds ctx dim t solver p = 
    let bs = extract_bounds dim p in
    let (uppers, lowers) = S.to_list (fst bs), S.to_list (snd bs) in
    let mk_z3_upper upper = cntsr_to_z3 `ge ctx (lt_add upper (lt_negate t)) in
    let mk_z3_lower lower = cntsr_to_z3 `ge ctx (lt_add t (lt_negate lower)) in
    let potential_bounds = (List.map mk_z3_upper uppers) @ (List.map mk_z3_lower lowers) in
    let true_bounds, _ = find_cons ctx solver potential_bounds in

    let partitioner (ups, lows, viol_ups, viol_lows, i) b = 
      if List.mem i true_bounds then
        if i < List.length uppers then S.add (List.nth uppers i) ups, lows, viol_ups, viol_lows, i+1
        else ups, S.add (List.nth lowers (i - (List.length uppers))) lows, viol_ups, viol_lows, i+1
      else
        if i < List.length uppers then ups, lows, b :: viol_ups, viol_lows, i+1
        else ups, lows, viol_ups, b :: viol_lows, i+1
    in
    let (real_ups, real_lows, violated_ups, violated_lows, _) = List.fold_left partitioner (S.empty, S.empty, [], [], 0) potential_bounds in
    real_ups, real_lows, violated_ups, violated_lows


  (*let pp_bounds is_lower t f bounds = 
    let pp_print_bound fo b = 
      Format.pp_open_hbox fo ();
      if is_lower then (pp_l fo t; Format.pp_print_string fo " >= "; pp_l fo b)
      else (pp_l fo t; Format.pp_print_string fo " <= "; pp_l fo b);
      Format.pp_close_box fo ()
    in
    Format.pp_open_vbox f 4;
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) pp_print_bound f bounds;
    Format.pp_close_box f ()*)


  let optimize_t_by_project t fresh_dim dims_in_ord poly ctx solver =
    let t_eq_D = DM.add fresh_dim (C.from_string_c "-1") (fst t), (snd t) in
    let poly_with_eq = add_cnstr `eq poly t_eq_D in
    Z3.Solver.push solver;
    Z3.Solver.add solver [cntsr_to_z3 `eq ctx t_eq_D];
    let rec find_optimal_conjectured_bound m rem_dims curr_poly = 
      (*Log.log_line_s ~level:`trace "Looking for conjectured bounds";
      Log.log ~level:`trace pp (Some curr_poly);*)
      if rem_dims = [] then collect_bounds fresh_dim curr_poly
      else
        match collect_bounds fresh_dim curr_poly with
        | NoBound -> NoBound
        | Upper (uppers) ->
          (match find_optimal_conjectured_bound m (List.tl rem_dims) (project_dim m curr_poly (List.hd rem_dims)) with
          | Upper (proj_uppers) -> Upper (proj_uppers)
          | Both (proj_bound) -> Both (proj_bound) (* I don't see how this case is possible*)
          | Lower (proj_lowers) -> Both (meet uppers proj_lowers)
          | NoBound -> Upper (uppers))
        | Lower (lowers)->
          (match find_optimal_conjectured_bound m (List.tl rem_dims) (project_dim m curr_poly (List.hd rem_dims)) with
          | Upper (proj_uppers) -> Both (meet lowers proj_uppers)
          | Both (proj_bound) -> Both (proj_bound) (* I don't see how this case is possible*)
          | Lower (proj_lowers) -> Lower (proj_lowers)
          | NoBound -> Lower (lowers))
        | Both (bounds) ->
          (match find_optimal_conjectured_bound m (List.tl rem_dims) (project_dim m curr_poly (List.hd rem_dims)) with
          | Upper (proj_uppers) -> Both (meet bounds proj_uppers)
          | Both (proj_bound) -> Both (proj_bound)
          | Lower (proj_lowers) -> Both (meet bounds proj_lowers)
          | NoBound -> Both bounds)
    in


    (*    let proj = project_dim m curr_poly (List.hd rem_dims) in
        match collect_bounds fresh_dim proj with
        | Both _ -> find_optimal_conjectured_bound m (List.tl rem_dims) proj
        | Upper 
 

      match has_bound fresh_dim curr_poly with
      | NoBound -> None
      | Both when rem_dims = [] ->
        let (pot_uppers, pot_lowers) = collect_bounds fresh_dim curr_poly in
        if S.is_empty pot_uppers && S.is_empty pot_lowers then None
        else Some (pot_uppers, pot_lowers, curr_poly)
      | Upper when rem_dims = [] ->
        let (pot_uppers, _) = collect_bounds fresh_dim curr_poly in
        if S.is_empty pot_uppers then None
        else Some (pot_uppers, S.empty, curr_poly)
      | Lower when rem_dims = [] ->
        let (_, pot_lowers) = collect_bounds fresh_dim curr_poly in
        if S.is_empty pot_lowers then None
        else Some (S.empty, pot_lowers, curr_poly)
      | Both ->
        (let proj = project_dim m curr_poly (List.hd rem_dims) in
        match find_optimal_conjectured_bound m (List.tl rem_dims) proj with
        | None -> 
          let (pot_uppers, pot_lowers) = collect_bounds fresh_dim curr_poly in
          if S.is_empty pot_uppers && S.is_empty pot_lowers then None (* This case should be impossible*)
          else Some (pot_uppers, pot_lowers, curr_poly)
        | Some (ups, lows, smaller_poly) when S.is_empty ups -> 
          let (this_level_ups, _) = collect_bounds fresh_dim curr_poly in
          Some (this_level_ups, lows, meet smaller_poly curr_poly)
        | Some (ups, lows, smaller_poly) when S.is_empty lows ->
          let (_, this_level_lows) = collect_bounds fresh_dim curr_poly in
          Some (ups, this_level_lows, meet smaller_poly curr_poly)
        | Some (ups, lows, smaller_poly) -> Some (ups, lows, meet smaller_poly curr_poly)
        )
      | Upper -> 
        (let proj = project_dim m curr_poly (List.hd rem_dims) in
        match find_optimal_conjectured_bound m (List.tl rem_dims) proj with
        | None -> 
          let (pot_uppers, _) = collect_bounds fresh_dim curr_poly in
          if S.is_empty pot_uppers then None (* This case should be impossible *)
          else Some (pot_uppers, S.empty, curr_poly)
        | Some (ups, lows, _) when S.is_empty ups -> (* Lows should be empty here *)
          let (pot_uppers, _) = collect_bounds fresh_dim curr_poly in
          Some (pot_uppers, lows, curr_poly)
        | Some (ups, lows, smaller_poly) -> Some(ups, lows, meet smaller_poly curr_poly)
        )
      | Lower ->
        (let proj = project_dim m curr_poly (List.hd rem_dims) in
        match find_optimal_conjectured_bound m (List.tl rem_dims) proj with
        | None -> 
          let (_, pot_lowers) = collect_bounds fresh_dim curr_poly in
          if S.is_empty pot_lowers then None (* This case should be impossible *)
          else Some (S.empty, pot_lowers, curr_poly)
        | Some (ups, lows, _) when S.is_empty lows -> (* Ups should be empty here *)
          let (_, pot_lowers) = collect_bounds fresh_dim curr_poly in
          Some (ups, pot_lowers, curr_poly)
        | Some (ups, lows, smaller_poly) -> Some(ups, lows, meet smaller_poly curr_poly)
        )
    in*)
    (*let env = A.int_list_to_env (fresh_dim :: dims_in_ord) in*)
    let rec find_optimal_real_bound (uppers, lowers) (searched_uppers, searched_lowers) = 
      if not (S.is_empty uppers) && not (S.is_empty lowers) then (S.to_list uppers, S.to_list lowers)
      else
        let dont_search = 
          if S.is_empty uppers && S.is_empty lowers then Z3.Boolean.mk_or ctx [Z3.Boolean.mk_and ctx searched_lowers; Z3.Boolean.mk_and ctx searched_uppers]
          else if S.is_empty uppers then Z3.Boolean.mk_and ctx searched_uppers
          else Z3.Boolean.mk_and ctx searched_lowers in
        (*let poly = A.to_poly curr_explored in*)
        (*Z3.Solver.add solver [Z3.Boolean.mk_not ctx (poly_to_z3 ctx poly)];*)
        match Z3.Solver.check solver [dont_search] with
        | Z3.Solver.UNKNOWN -> failwith "Z3 solver returned unknown"
        | Z3.Solver.UNSATISFIABLE ->
          S.to_list uppers, S.to_list lowers
        | Z3.Solver.SATISFIABLE ->
          (match Z3.Solver.get_model solver with
            | None -> failwith "Error getting model"
            | Some model ->
              let m = z3_model_to_dm model in
              let explored_region = find_optimal_conjectured_bound m dims_in_ord poly_with_eq in
              match explored_region with
              | NoBound | Upper _ | Lower _ -> failwith "Polyhedron has no conjectured bounds"
              | Both p -> 
                (*let p = A.to_poly (A.of_poly env p) in*)
                Log.log_line_s ~level:`trace "Conjectured bounds";
                Log.log ~level:`trace pp (Some p);
                let (real_uppers, real_lowers, unreal_uppers, unreal_lowers) = check_bounds ctx fresh_dim t solver p in
                let next_unreal_uppers = List.map (Z3.Boolean.mk_not ctx) unreal_uppers @ searched_uppers in
                let next_unreal_lowers = List.map (Z3.Boolean.mk_not ctx) unreal_lowers @ searched_lowers in
                find_optimal_real_bound (S.union real_uppers uppers, S.union real_lowers lowers) (next_unreal_uppers, next_unreal_lowers))
    in



            (*match find_optimal_conjectured_bound m dims_in_ord poly_with_eq with
            | None -> failwith "Added fictitious dimension is unbounded"
            | Some (pot_uppers, pot_lowers, smallest_poly) ->
              Log.log_line_s ~level:`trace "Conjectured Bounds:";
              Log.log ~level:`trace (pp_bounds false t) (Some (S.to_list pot_uppers));
              Log.log ~level:`trace (pp_bounds true t) (Some (S.to_list pot_lowers));
              let (real_uppers, real_lowers) = check_bounds ctx (S.to_list pot_uppers) (S.to_list pot_lowers) t solver in
              if not (S.is_empty real_uppers) || not (S.is_empty real_lowers) then
                (Log.log_line_s ~level:`trace "Found Real bounds";
                Log.log ~level:`trace (pp_bounds false t) (Some (S.to_list real_uppers));
                Log.log ~level:`trace (pp_bounds true t) (Some (S.to_list real_lowers)))
              else Log.log_line_s ~level:`trace "None were real bounds";
              find_optimal_real_bound (S.union real_uppers found_uppers, S.union real_lowers found_lowers) (smallest_poly :: areas_expored)            
          )
    
    
     (found_uppers, found_lowers) areas_expored = 
      if not (S.is_empty found_uppers) && not (S.is_empty found_lowers) then 
        (Log.log_line_s ~level:`trace "All found bounds";
        Log.log ~level:`trace (pp_bounds false t) (Some (S.to_list found_uppers));
        Log.log ~level:`trace (pp_bounds true t) (Some (S.to_list found_lowers));
        (S.to_list found_uppers, S.to_list found_lowers))
      else
        let not_in_searched = 
          if areas_expored = [] then Z3.Boolean.mk_true ctx
          else Z3.Boolean.mk_not ctx (Z3.Boolean.mk_or ctx (List.map (poly_to_z3 ctx) areas_expored)) in


        match Z3.Solver.check solver [not_in_searched] with
        | Z3.Solver.UNKNOWN | Z3.Solver.UNSATISFIABLE -> failwith "Unsat polyhedron"
        | Z3.Solver.SATISFIABLE ->
          (match Z3.Solver.get_model solver with
          | None -> failwith "Error getting model"
          | Some model ->
            let m = z3_model_to_dm model in
            match find_optimal_conjectured_bound m dims_in_ord poly_with_eq with
            | None -> failwith "Added fictitious dimension is unbounded"
            | Some (pot_uppers, pot_lowers, smallest_poly) ->
              Log.log_line_s ~level:`trace "Conjectured Bounds:";
              Log.log ~level:`trace (pp_bounds false t) (Some (S.to_list pot_uppers));
              Log.log ~level:`trace (pp_bounds true t) (Some (S.to_list pot_lowers));
              let (real_uppers, real_lowers) = check_bounds ctx (S.to_list pot_uppers) (S.to_list pot_lowers) t solver in
              if not (S.is_empty real_uppers) || not (S.is_empty real_lowers) then
                (Log.log_line_s ~level:`trace "Found Real bounds";
                Log.log ~level:`trace (pp_bounds false t) (Some (S.to_list real_uppers));
                Log.log ~level:`trace (pp_bounds true t) (Some (S.to_list real_lowers)))
              else Log.log_line_s ~level:`trace "None were real bounds";
              find_optimal_real_bound (S.union real_uppers found_uppers, S.union real_lowers found_lowers) (smallest_poly :: areas_expored)            
          )
    in*)
    find_optimal_real_bound (S.empty, S.empty) ([Z3.Boolean.mk_true ctx], [Z3.Boolean.mk_true ctx])
end
