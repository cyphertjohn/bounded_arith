let (%) = BatPervasives.(%)


module Make(P : Poly.Polynomial) = struct
  module Cl = Closure.Make(P)
  include P
  
  type impl = poly * poly

  let (=>) p q : impl = (p, q)

  (*
  type conein = {
    ord : monic_mon -> monic_mon -> int;
    eqs : poly list;
    ineqs : poly list;
    impls : impl list
  }
  *)

  (*type eqJust = 
    {
      orig : poly;
      mults : poly list
    }*)
  
  (*type posCom = PosComb of ((int * coef) list * I.coef)

  type derJust = eqJust * posCom*)

  type justification = 
   | Product of int list
   | Given

  type cone = 
    {
      z3ctx : Z3.context;
      depth : int;
      closure : Cl.closure;
      curr_poly : int;
      ineqs : ((C.coef BatIMap.t) * justification) BatIMap.t;
      ineqs_prod : int list list list
    }

  let make_empty_cone depth closure =
    {z3ctx = Z3.mk_context []; depth; closure; curr_poly = 0; ineqs = BatIMap.empty ~eq:(fun _ _ -> false); ineqs_prod = []}


  let poly_to_dim p =
    let mons = get_mons p in
    if mons = [] then
      let (zero, zero_monic) = zero_mon in
      BatIMap.singleton ~eq:(fun a b -> C.cmp a b = 0) (mon_to_id zero_monic) zero
    else
      List.fold_left (fun map (coe, monic) -> BatIMap.add (mon_to_id monic) coe map) (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) mons

  let dim_to_poly dim_map = 
    from_mon_list (BatIMap.fold (fun dim coe l -> (coe, id_to_mon dim) :: l) dim_map [])

  (*let get_eq_basis c = I.get_generators c.ideal*)

  let get_ineq_basis c = 
    if List.length c.ineqs_prod = 0 then [from_const_s "0"]
    else
      let first_level = List.map List.hd (List.hd c.ineqs_prod) in
      List.map (fun i -> (dim_to_poly (fst (BatIMap.find i c.ineqs)))) first_level


  let ppc f c = 
      Format.pp_print_string f "Closure:"; Format.pp_print_space f ();
      Cl.pp_c f c.closure;
      Format.pp_force_newline f ();
      if BatIMap.is_empty c.ineqs then Format.pp_print_string f "Ineqs: [0]"
      else
        Format.pp_open_hbox f ();
        Format.pp_print_string f "Basis Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp ~ord:(Cl.get_ord c.closure)) f (get_ineq_basis c);
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ()(*
        Format.pp_force_newline f ();
        Format.pp_open_hbox f ();
        Format.pp_print_string f "Derived Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp ~ord:c.ideal.ord) f (BatList.of_enum (BatEnum.map (fun (_, _, (i, _)) -> dim_to_poly c i) (BatIMap.enum c.ineqs)));
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ()*)


  (*type cone = int * I.ideal * poly list list*)

  let is_const_not_neg p = 
    match is_const p with
    | Some c ->
      if C.cmp c C.zero >= 0 then Some c
      else None
    | None -> None


  let upgrade_ineqs c ineqs_to_upgrade = 
    let is_factor a b = 
      let rec aux xl yl = 
        match xl, yl with
        | [], [] -> true
        | _, [] -> false
        | [], _ -> true
        | x :: xs, y :: ys ->
          if x = y then aux xs ys
          else if y < x then false
          else aux xl ys
      in
      aux a b
    in
    let ineqs_to_prods lis = List.map (fun id -> 
      match BatIMap.find id c.ineqs with
      | (_, Given) -> [id]
      | (_, Product l) -> l
    ) lis in
    let ineqs_to_upgrade_prods = ineqs_to_prods ineqs_to_upgrade in
    let collect_ineqs_to_remove id (_, just) to_remove = 
      match just with
      | Product prods ->
        if List.exists (fun remove_pset -> is_factor remove_pset prods) ineqs_to_upgrade_prods then id :: to_remove
        else to_remove
      | _ -> to_remove
    in
    let ineqs_to_remove = BatIMap.fold collect_ineqs_to_remove c.ineqs ineqs_to_upgrade in
    let new_ineqs = List.fold_left (fun m i -> BatIMap.remove i m) c.ineqs ineqs_to_remove in
    let new_eqs = List.map (fun id -> dim_to_poly (fst (BatIMap.find id c.ineqs))) ineqs_to_upgrade in
    let new_cl = Cl.add_eqs new_eqs c.closure in
    let folder id (ineq, just) (map, remove) = 
      let new_red, new_just = 
        match just with
        | Product prod_list -> 
          let p_red = Cl.reduce (dim_to_poly ineq) new_cl in
          p_red, Product prod_list
        | Given -> 
          let p_red = Cl.reduce (dim_to_poly ineq) new_cl in
          p_red, Given 
      in
      match is_const new_red with
      | None -> BatIMap.add id (poly_to_dim new_red, new_just) map, remove
      | Some c ->
        if C.cmp c C.zero >= 0 then (map, id :: remove)
        else failwith "Created a contradiction"
    in
    let red_ineqs, is_to_remove = BatIMap.fold folder new_ineqs (BatIMap.empty ~eq:(fun _ _ -> false), ineqs_to_remove) in
    let is_to_remove_prod = ineqs_to_prods is_to_remove in
    let new_ineq_prod = List.map (fun pll -> List.filter (fun pl -> not (List.exists (fun r -> is_factor r pl) is_to_remove_prod)) pll) c.ineqs_prod in
    {c with closure = new_cl; ineqs = red_ineqs; ineqs_prod = new_ineq_prod}



  (* This function doesn't check whether incoming ine is already a member of the linear cone. Could consider an alternative*)
  let add_ineq c ine just : (cone * int list) = 
    let mult_and_minimize_ineqs (ineqs, curr_id) ins_to_add = 
      let reduce_and_just (inequs, id) prod = 
        let p = List.fold_left (fun acc ind -> mul acc (dim_to_poly (fst (BatIMap.find ind inequs)))) (from_const C.one) prod in
        let p_red = Cl.reduce p c.closure in
        match is_const_not_neg p_red with
        | Some _ -> inequs, id
        | None ->
          let new_ineqs = BatIMap.add id (poly_to_dim p_red, Product prod) inequs in
          new_ineqs, (id + 1)
      in
      List.fold_left reduce_and_just (ineqs, curr_id) ins_to_add
    in
    if not (is_const_not_neg ine = None) then c, []
    else if BatIMap.is_empty c.ineqs then 
      let poly_id = c.curr_poly in
      let rec dup v t = if t <=0 then [] else v :: (dup v (t-1)) in
      let rec aux acc depth = 
        if depth <= 0 then acc
        else 
          aux ([dup poly_id depth] :: acc) (depth - 1)
      in
      let ineq_ladder = aux [] c.depth in
      let prod_to_comput = List.concat (List.tl ineq_ladder) in
      let ine_map = poly_to_dim ine in
      let ineqs, next_id = mult_and_minimize_ineqs ((BatIMap.add poly_id (ine_map, just) (BatIMap.empty ~eq:(fun _ _ -> false))), poly_id + 1) prod_to_comput in
      {c with curr_poly = next_id; ineqs; ineqs_prod = ineq_ladder}, List.init (next_id - poly_id) (fun i -> poly_id + i)
    else 
      let poly_id = c.curr_poly in
      let folder (all_ineq, new_ineqs) curr_level = 
        if List.length all_ineq = 0 then [[poly_id] :: curr_level], new_ineqs
        else
          let prev_level = List.hd all_ineq in
          let new_ineq = List.map (fun p -> poly_id :: p) prev_level in
          (new_ineq @ curr_level) :: all_ineq, new_ineq @ new_ineqs
      in
      let ineqs_with_ine = BatIMap.add poly_id (poly_to_dim ine, just) c.ineqs in
      let ineqs_ladder, ineqs_to_add = List.fold_left folder ([], []) c.ineqs_prod in
      let ineqs, next_id = mult_and_minimize_ineqs (ineqs_with_ine, poly_id + 1) ineqs_to_add in
      {c with curr_poly = next_id; ineqs; ineqs_prod = List.rev ineqs_ladder}, List.init (next_id - poly_id) (fun i -> poly_id + i)


  let find_cons ctx solver pot_cons biggest_flag_num = 
    (*Z3.Solver.push solver;*)
    let pot_cons_with_flags = List.mapi (fun i c -> (i, Z3.Boolean.mk_const_s ctx ("b" ^ (string_of_int (i + biggest_flag_num))), c)) pot_cons in
    let round_f = Z3.Boolean.mk_const_s ctx ("r" ^ (string_of_int biggest_flag_num)) in
    Z3.Solver.add solver [Z3.Boolean.mk_implies ctx round_f (Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags)))];
    Z3.Solver.add solver [Z3.Boolean.mk_not ctx (Z3.Boolean.mk_and ctx (List.map (fun (_, b, c) -> Z3.Boolean.mk_implies ctx b c) pot_cons_with_flags))];
    let rec aux cons_in_play cons_violated = 
      let assumpts = List.concat (List.map (fun (_, clist) -> List.map (fun (_, b, _) -> Z3.Boolean.mk_not ctx b) clist) cons_violated) in
      match Z3.Solver.check solver (round_f :: assumpts) with
      | Z3.Solver.UNKNOWN -> failwith "Error in z3 solver"
      | Z3.Solver.UNSATISFIABLE -> 
        (*Z3.Solver.pop solver 1;*)
        Z3.Solver.add solver (List.map (fun (_, _, c) -> c) cons_in_play);
        Z3.Solver.add solver [Z3.Boolean.mk_not ctx round_f];
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


  (*let ppmodel c f model = 
    let model_interps = 
      List.fold_left (fun acc fun_decl -> 
        if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then acc (* Not a general solution *)
        else
          let interp = match Z3.Model.get_const_interp model fun_decl with
          | None -> failwith "Const has no interpretation in model"
          | Some e-> 
            Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
          in
          (get_mon c (Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl)), interp) :: acc) [] (Z3.Model.get_const_decls model) in
    Format.pp_open_hvbox f 0;
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) (fun fo (monic, interp) -> ppmm fo monic; Format.pp_print_string fo (" = " ^ (Mon.to_string_c interp))) f model_interps
    *)
    

  let complete_and_evaluate_model m new_ineqs form c = 
    let model_interps = 
      List.fold_left (fun map fun_decl -> 
        if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then map (* Not a general solution *)
        else
          let interp = match Z3.Model.get_const_interp m fun_decl with
          | None -> failwith "Const has no interpretation in model"
          | Some e-> 
            C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
          in
          BatIMap.add (Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl)) interp map) (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) (Z3.Model.get_const_decls m) in
    let folder interp_map new_ineq_id = 
      match BatIMap.find new_ineq_id c.ineqs with
      | (_, Product prod_list) ->
        let prod_folder prod_map prod_id = 
          let prod_coef_map, _ = BatIMap.find prod_id c.ineqs in
          let mon_prod_folder modeldim curr_interp acc =
            let mon_mon_folder dim _ inner_map = 
              let mon1 = id_to_mon dim in
              if is_one (from_mon_list [(C.one, mon1)]) then inner_map
              else
                let mon2 = id_to_mon modeldim in
                let model_interp = 
                  try C.mulc curr_interp (BatIMap.find dim model_interps)
                  with Not_found ->
                    failwith ("Don't have an interp for " ^ (to_string (from_mon_list [(C.one, mon1)]))) in
                let (_, prod_mon) = mult_mon (C.one, mon1) (C.one, mon2) in
                let prod_dim = mon_to_id prod_mon in
                if BatIMap.mem prod_dim inner_map || BatIMap.mem prod_dim model_interps then inner_map
                else BatIMap.add prod_dim model_interp inner_map
            in
            BatIMap.fold mon_mon_folder prod_coef_map acc
          in
          BatIMap.fold mon_prod_folder prod_map (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0))
        in
        let ineq_interps = List.fold_left prod_folder (fst (BatIMap.find (List.hd prod_list) c.ineqs)) (List.tl prod_list) in
        BatIMap.union (fun a _ -> a) interp_map ineq_interps
      | _ -> failwith "only know how to complete products"
    in
    let new_mon_interps = List.fold_left folder (BatIMap.empty ~eq:(fun a b -> C.cmp a b = 0)) new_ineqs in
    let partial_eval = match Z3.Model.eval m form false with | None -> failwith "Error evaluating model" | Some e -> e in
    let rem_consts = get_z3_consts partial_eval in
    let get_interps dim = 
      try 
        Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim), Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c (BatIMap.find dim new_mon_interps))
      with Not_found -> Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim), Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0
    in
    let vars, interps = List.split (List.map get_interps (BatISet.elements rem_consts)) in
    Z3.Expr.simplify (Z3.Expr.substitute partial_eval vars interps) None

  let saturate (c : cone) (impls : impl list) =
    let impls_red = 
      List.map 
        (fun (h, cons) -> (Cl.reduce h c.closure, Cl.reduce cons c.closure)) impls
    in
    let const_dim = mon_to_id (snd (make_mon_from_coef (C.zero))) in
    let dim_map_to_z3_ineq ineq = 
      let term_to_z3 dim coef = 
        if dim = const_dim then Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef)
        else
          Z3.Arithmetic.mk_mul c.z3ctx [Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef); Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim)]
      in
      Z3.Arithmetic.mk_ge c.z3ctx (Z3.Arithmetic.mk_add c.z3ctx (BatIMap.fold (fun d i l -> (term_to_z3 d i) :: l) ineq [])) (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)
    in
    let dim_map_to_z3_eq ineq = 
      let term_to_z3 dim coef = 
        if dim = const_dim then Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef)
        else
          Z3.Arithmetic.mk_mul c.z3ctx [Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef); Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim)]
      in
      Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.mk_add c.z3ctx (BatIMap.fold (fun d i l -> (term_to_z3 d i) :: l) ineq [])) (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)
    in
    let solver = Z3.Solver.mk_simple_solver c.z3ctx in
    Z3.Solver.add solver (BatList.of_enum (BatEnum.map (fun (_, _, (i, _)) -> dim_map_to_z3_ineq i) (BatIMap.enum c.ineqs)));
    let z3_impls = List.map (fun (h, cons) -> dim_map_to_z3_ineq (poly_to_dim h), dim_map_to_z3_ineq (poly_to_dim cons)) impls_red in
    Z3.Solver.add solver (List.map (fun (h, cons) -> Z3.Boolean.mk_implies c.z3ctx h cons) z3_impls);
    let pot_ineqs = List.mapi (fun i (_, cons) -> (i, cons, true)) z3_impls in
    let pot_eqs = BatList.of_enum (BatEnum.map (fun (id, _, (i, _)) -> id, dim_map_to_z3_eq i, false) (BatIMap.enum c.ineqs)) in
    let rec find_all_cons cons_in_play cons_not_in_play curr_num co = 
      Log.log_line_s ~level:`trace "Curr cone";
      Log.log ppc ~level:`trace (Some co);
      let cons, violated_cons_and_models = find_cons co.z3ctx solver (List.map (fun (_, f, _) -> f) cons_in_play) curr_num in
      if cons = [] then co
      else
        let found_cons = List.map (List.nth cons_in_play) cons in
        let num_found = ref 0 in
        let sort_cons_found_cons (cone, found_eqs, new_pot_eqs, new_ineqs) (id, _, is_ineq) = 
          if is_ineq then
            (num_found := !num_found + 1;
            let (_, ineq_to_add) = List.nth impls_red id in
            let conee, added = add_ineq cone ineq_to_add Given in
            let (added_id, non_lin) = match added with | [] -> failwith "Added no ineqs?" | x :: xs -> x, xs in
            let added_ineqs = (List.map (fun id -> dim_map_to_z3_ineq (fst (BatIMap.find id conee.ineqs))) non_lin) in
            Z3.Solver.add solver added_ineqs;
            let pot_eqs = (added_id, dim_map_to_z3_eq (fst (BatIMap.find added_id conee.ineqs)), false) :: List.map (fun id -> id, dim_map_to_z3_eq (fst (BatIMap.find id conee.ineqs)), false) non_lin in
            (conee, found_eqs, pot_eqs @ new_pot_eqs, non_lin @ new_ineqs))
          else
            (cone, id :: found_eqs, new_pot_eqs, new_ineqs)
        in
        let temp_cone, found_eqs, new_pot_eqs, new_ineqs = List.fold_left sort_cons_found_cons (co, [], [], []) found_cons in
        let cons_not_in_play_with_models = cons_not_in_play @ (List.map (fun (m, clist) -> m, (List.map (fun i -> List.nth cons_in_play i) clist)) violated_cons_and_models) in
        let new_ineqs_conj = Z3.Boolean.mk_and temp_cone.z3ctx (List.map (fun id -> dim_map_to_z3_ineq (fst (BatIMap.find id temp_cone.ineqs))) new_ineqs) in
        let (cons_not_in_play_this_round, new_pot_cons) = 
          List.partition (fun (m, _) -> 
            Z3.Boolean.is_true (complete_and_evaluate_model m new_ineqs new_ineqs_conj temp_cone)) cons_not_in_play_with_models in
        Log.log_line_s ~level:`trace ("Found " ^ (string_of_int !num_found) ^ " new consequences");
        Log.log_line_s ~level:`trace ("Found " ^ (string_of_int (List.length found_eqs)) ^ " new equations");
        Log.log_line_s ~level:`trace ((string_of_int (List.length cons_not_in_play_this_round)) ^ " old cons are still violated in new form");
        find_all_cons (List.concat (new_pot_eqs :: List.map snd new_pot_cons)) cons_not_in_play_this_round (curr_num + List.length cons_in_play) (upgrade_ineqs temp_cone found_eqs)
    in
    find_all_cons (pot_eqs @ pot_ineqs) [] 0 c


  let preprocess_ineqs p c = 
    let (_, lm) = lt (make_sorted_poly (Cl.get_ord c.closure) p) in
    let const_dim = mon_to_id (snd (make_mon_from_coef (C.zero))) in
    let folder id (ineq, _) (consts, parity_map) = 
      let ineq_list = List.sort (fun i j -> (-1) * ((Cl.get_ord c.closure) (id_to_mon i) (id_to_mon j))) (BatISet.elements (BatIMap.domain ineq)) in
      if List.length ineq_list = 0 then (id :: consts, parity_map)
      else if List.length ineq_list = 1 && const_dim = List.hd ineq_list then 
        let dim_coef = BatIMap.find (List.hd ineq_list) ineq in
        if C.cmp dim_coef C.zero < 0 then failwith "Negative const in polyhedron"
        else (id :: consts, parity_map)
      else
        let bigger_mons = List.filter (fun i -> (Cl.get_ord c.closure) (id_to_mon i) lm > 0) ineq_list in
        let update_map map dim = 
          if BatIMap.mem dim map then
            (match BatIMap.find dim map with
            | None -> map
            | Some par -> 
              let dim_coef = BatIMap.find dim ineq in
              if C.cmp dim_coef C.zero = 0 then failwith "ineq has 0 coeficient";
              let dim_par = if C.cmp dim_coef C.zero > 0 then 1 else (-1) in
              if par = dim_par then map
              else BatIMap.modify dim (fun _ -> None) map)
          else
            let dim_coef = BatIMap.find dim ineq in
            if C.cmp dim_coef C.zero = 0 then failwith "ineq has 0 coeficient";
            let dim_par = if C.cmp dim_coef C.zero > 0 then 1 else (-1) in
            BatIMap.add dim (Some dim_par) map
        in
        (consts, List.fold_left update_map parity_map bigger_mons)
    in
    let (const_ineqs, parity_map) = BatIMap.fold folder c.ineqs ([], BatIMap.empty ~eq:(=)) in
    let collect_irrelevant_dims dim par irrelevant_dims =
      match par with
      | None -> irrelevant_dims
      | Some _ -> dim :: irrelevant_dims
    in
    let irrelevant_dims = BatIMap.fold collect_irrelevant_dims parity_map [] in
    let find_ineq_to_remove id (ineq, _) ineqs_to_remove = 
      if List.exists (fun dim -> BatIMap.mem dim ineq) irrelevant_dims then id :: ineqs_to_remove
      else ineqs_to_remove
    in
    let ineqs_to_remove = BatIMap.fold find_ineq_to_remove c.ineqs const_ineqs in
    Log.log_line_s ~level:`trace ("Preprocessing removed " ^ (string_of_int (List.length ineqs_to_remove)) ^ " ineqs");
    List.fold_left (fun map id_to_remove-> BatIMap.remove id_to_remove map) c.ineqs ineqs_to_remove

  let reduce_ineq p c = 
    match is_const p with
    | Some _ -> [], p
    | None ->
      let preprocessed_ineqs = preprocess_ineqs p c in
      let ids = BatISet.elements (BatIMap.domain preprocessed_ineqs) in
      if List.length ids = 0 then [], p
      else 
        let solver = Z3.Optimize.mk_opt c.z3ctx in
        let folder id (ineq, _) (dim_sum_map, ls) = 
          let lambda = Z3.Arithmetic.Real.mk_const_s c.z3ctx ("lambda" ^ (string_of_int id)) in
          let collect_ineq_dims dim coef map = 
            BatIMap.modify_opt dim
              (fun old_e ->
                match old_e with
                | None -> Some (Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef))])
                | Some e -> Some (Z3.Arithmetic.mk_add c.z3ctx [e; Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef))]])
              ) map
          in
          Z3.Optimize.add solver [Z3.Arithmetic.mk_le c.z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)];
          BatIMap.fold collect_ineq_dims ineq dim_sum_map, lambda :: ls
        in
        let dim_sum_map, lambdas = BatIMap.fold folder preprocessed_ineqs (BatIMap.empty ~eq:(fun _ _ -> false), []) in
        Log.log_line_s ~level:`trace (string_of_int (BatISet.cardinal (BatIMap.domain dim_sum_map)) ^ " dimensions");
        Log.log_line_s ~level:`trace ((string_of_int (List.length lambdas)) ^ " ineqs");
        let p_dim_map = poly_to_dim p in
        let dims_sorted_small_to_big = 
          List.sort (fun i_dim j_dim -> (Cl.get_ord c.closure) (id_to_mon i_dim) (id_to_mon j_dim)) 
            (BatISet.elements (BatISet.union (BatIMap.domain dim_sum_map) (BatIMap.domain p_dim_map))) in
        let dims_and_r_cons = List.map
          (fun dim -> 
            let r = Z3.Arithmetic.Real.mk_const_s c.z3ctx ("r" ^ (string_of_int dim)) in
            if BatIMap.mem dim p_dim_map && BatIMap.mem dim dim_sum_map then
              (let p_coef = BatIMap.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c p_coef)) (Z3.Arithmetic.mk_add c.z3ctx [r; BatIMap.find dim dim_sum_map])]; (* p_c = sum lambda_i + r *)
              (dim, r))
            else if BatIMap.mem dim p_dim_map then
              (let p_coef = BatIMap.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c p_coef)) r]; (* p_c = r*)
              (dim, r))
            else
              (Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0) (Z3.Arithmetic.mk_add c.z3ctx [r; BatIMap.find dim dim_sum_map])]; (* 0 = sum lambda_i + r*)
              (dim, r))
          ) dims_sorted_small_to_big in
        List.iter (fun (dim, r) -> let _ = Z3.Optimize.add_soft solver (Z3.Boolean.mk_eq c.z3ctx r (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)) "1" (Z3.Symbol.mk_int c.z3ctx dim) in ()) (List.rev dims_and_r_cons);
        let _ = Z3.Optimize.maximize solver (Z3.Arithmetic.mk_add c.z3ctx lambdas) in
        match Log.log_time_cum "z3 solve reduction" Z3.Optimize.check solver with
        | Z3.Solver.UNKNOWN | Z3.Solver.UNSATISFIABLE -> failwith "unable to solve linear program"
        | Z3.Solver.SATISFIABLE ->
          match Z3.Optimize.get_model solver with
          | None -> failwith "Z3 has no model"
          | Some model ->
            (*let collect_lambdas neg_comb (lambda, ineq_id) = 
              match (Z3.Model.get_const_interp_e model lambda) with
              | None -> failwith "Z3 model doesn't have a lambda"
              | Some lc ->
                let lambdac = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio lc) in
                if Mon.cmp lambdac (Mon.from_string_c "0") = 0 then neg_comb
                else
                  (lambdac, ineq_id) :: neg_comb
            in
            let neg_comb = List.fold_left collect_lambdas [] ineq_dim_lambda in*)
            let collect_remainder rem (r_dim, r_e) = 
              match (Z3.Model.get_const_interp_e model r_e) with
              | None -> failwith "Z3 model doesn't have an r"
              | Some rv ->
                let rc = C.of_zarith_q (Z3.Arithmetic.Real.get_ratio rv) in
                if C.cmp rc (C.from_string_c "0") = 0 then rem
                else
                  (rc, id_to_mon r_dim) :: rem
            in
            let rem = from_mon_list (List.fold_left collect_remainder [] dims_and_r_cons) in
            [], rem
        
  (*let reduce_eq p c = Cl.reduce p c.closure*)

  let reduce p c = 
    let p_ired (*mults*) = Log.log_time_cum "reduce eq" (Cl.reduce p) c.closure in
    let (*neg_comb*)_, p_ineq_red = Log.log_time_cum "reduce ineq" (reduce_ineq p_ired) c in
    (*let eq_just = {orig = p_ired; mults} in
    Log.log ~level:`debug pp_red (Some (eq_just, neg_comb, p_ineq_red, c));*)
    p_ineq_red
    

  (*let saturate c impls = 
    let rec aux curr_cone worklist tried = 
      match worklist with
      | [] -> curr_cone
      | (imp, con) :: rest ->
        match is_non_neg imp curr_cone with
        | None -> aux curr_cone rest ((imp, con) :: tried)
        | Some just ->
           let con_red, mults = I.reduce_just con c.ideal in
           let eq_just = {orig = con; mults} in
           aux (add_ineq curr_cone con_red (Given (eq_just, (Some just)))) (rest @ tried) []
    in
    aux c impls []*)

  
  (*let make_cone ?(sat = 1) ?(ord = I.grlex_ord) ?(eqs = []) ?(ineqs = []) ?(impls = []) () = 
    let ideal = make_ideal ord eqs in
    let red_add_ine co ine = 
      let ine_red, mults = I.reduce_just ine co.ideal in
      let eq_just = {orig = ine_red; mults} in
      fst (add_ineq co ine_red (Given (eq_just)))
    in
    let prod_sat_cone = List.fold_left red_add_ine (make_empty_cone sat ideal) ineqs in
    let unnormal_c = saturate prod_sat_cone impls in
    (*normalize unnormal_c*)
    unnormal_c*)

  let make_cone_cl ?(sat = 1) ?(ineqs = []) ?(impls = []) cl = 
    let ineqs = ineqs @ (Cl.instantiate_ineqs cl) in
    let impls = impls @ (Cl.instantiate_impls cl) in
    let red_add_ine co ine = 
      let ine_red = Cl.reduce ine co.closure in
      fst (add_ineq co ine_red (Given))
    in
    let prod_sat_cone = 
      Log.log_time_cum "prod sat" (List.fold_left red_add_ine (make_empty_cone sat cl)) ineqs in
    let unnormal_c = Log.log_time_cum "impl sat" (saturate prod_sat_cone) impls in
    (*Log.log_time_cum "normalize" normalize unnormal_c*)
    unnormal_c
  

  let unpurify p con = Cl.unpurify p con.closure

end