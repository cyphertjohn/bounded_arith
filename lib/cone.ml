let (%) = BatPervasives.(%)


module Make(P : Poly.Polynomial) = struct
  module Cl = Closure.Make(P)
  include P
  
  module MS = struct
    type set = BatISet.t include BatISet 
    
    let add v s = BatISet.add (mon_to_id v) s
      
    let mem v s = BatISet.mem (mon_to_id v) s

    let fold f s = BatISet.fold (fun a b -> f (id_to_mon a) b) s

    let to_list s = List.map id_to_mon (BatISet.elements s)
  end

  module MM = struct
    module B = BatMap.Make(struct type t = monic_mon let compare a b= Int.compare (mon_to_id a) (mon_to_id b) end)
    type 'a map = 'a B.t
    include B
    let domain m = BatEnum.fold (fun s (a, _) -> MS.add a s) MS.empty (B.enum m)
  end

  module IM = BatMap.Make(Int)

  type impl = poly * poly

  let (=>) p q : impl = (p, q)

  (*type eqJust = 
    {
      orig : poly;
      mults : poly list
    }*)
  
  (*type posCom = PosComb of ((int * coef) list * I.coef)

  type derJust = eqJust * posCom*)

  type ineq =
    {
      dm : C.coef MM.map;
      d : int;
      prod : int list;
      is_strict : bool
    }

  type cone = 
    {
      z3ctx : Z3.context;
      depth : int;
      closure : Cl.closure;
      curr_poly : int;
      ineqs : ineq IM.t;
    }

  let make_empty_cone depth closure =
    {z3ctx = Z3.mk_context []; depth; closure; curr_poly = 0; ineqs = IM.empty}


  let poly_to_dim p =
    let mons = get_mons p in
    if mons = [] then
      let (zero, zero_monic) = zero_mon in
      MM.singleton (zero_monic) zero
    else
      List.fold_left (fun map (coe, monic) -> MM.add monic coe map) MM.empty mons

  let dim_to_poly dim_map = 
    from_mon_list (MM.fold (fun dim coe l -> (coe, dim) :: l) dim_map [])

  (*let get_eq_basis c = I.get_generators c.ideal*)

  (*let get_ineq_basis c = 
    let basis = IM.fold (fun _ ineq b -> if ineq.d = 1 then ineq :: b else b) c.ineqs [] in
    basis*)

  let pp_ine ord f ine = 
    Format.pp_open_hbox f (); pp f ~ord:ord (dim_to_poly ine.dm);
    if ine.is_strict then Format.pp_print_string f " > 0"
    else Format.pp_print_string f " >=0 ";
    Format.pp_close_box f ()


  let ppc f c = 
      Format.pp_print_string f "Closure:"; Format.pp_print_space f ();
      Cl.pp_c f c.closure;
      Format.pp_force_newline f ();
      if IM.is_empty c.ineqs then Format.pp_print_string f "Ineqs: [0]"
      else
        ((*Format.pp_open_hbox f ();
        Format.pp_print_string f "Basis Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_vbox f 4;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp_ine (Cl.get_ord c.closure)) f (get_ineq_basis c);
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ();
        Format.pp_force_newline f ();
        Format.pp_open_hbox f ();*)
        Format.pp_open_hbox f ();
        Format.pp_open_vbox f 4;
        Format.pp_print_string f "Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        let pp_ine_id fo (id, ine) = 
          Format.pp_open_hbox fo ();
          Format.pp_print_int fo id;
          Format.pp_print_string fo ": ";
          pp_ine (Cl.get_ord c.closure) fo ine;
          Format.pp_close_box fo ()
        in
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp_ine_id) f (BatList.of_enum ( (IM.enum c.ineqs)));
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ())


  (*type cone = int * I.ideal * poly list list*)



  let reduce_ineqs c = 
    let folder id ineq (new_ineqs, modified) = 
      let ineq_red, redocc = Cl.reduce (dim_to_poly ineq.dm) c.closure in
      match is_const ineq_red with 
      | None -> 
        if redocc then IM.add id {ineq with dm = poly_to_dim ineq_red} new_ineqs, id :: modified
        else IM.add id ineq new_ineqs, modified
      | Some c ->
        let c_cmp = C.cmp c C.zero in
        if c_cmp < 0 then failwith "Created a contradiction. An assumption is less than 0"
        else if c_cmp = 0 && ineq.is_strict then failwith "Created a contradiction. A strict assumption is equal to 0"
        else new_ineqs, modified
    in
    let new_ines, modified = IM.fold folder c.ineqs (IM.empty, []) in
    {c with ineqs = new_ines}, modified


  let upgrade_ineqs c ineqs_to_upgrade eqs_to_add = 
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
      let ine =  IM.find id c.ineqs in
      ine.prod
    ) lis in
    let ineqs_to_upgrade_prods = ineqs_to_prods ineqs_to_upgrade in
    let collect_ineqs_to_remove id ineq to_remove = 
      if List.exists (fun remove_pset -> is_factor remove_pset ineq.prod) ineqs_to_upgrade_prods then
        if ineq.is_strict then failwith "Reduced a strict ineq to 0. I.e 0 > 0"
        else id :: to_remove
      else to_remove
    in
    let ineqs_to_remove = IM.fold collect_ineqs_to_remove c.ineqs ineqs_to_upgrade in
    let new_ineqs = List.fold_left (fun m i -> IM.remove i m) c.ineqs ineqs_to_remove in
    let new_eqs = List.map (fun id -> dim_to_poly (IM.find id c.ineqs).dm) ineqs_to_upgrade in
    let new_cl = Cl.add_eqs (new_eqs @ eqs_to_add) c.closure in
    reduce_ineqs {c with closure = new_cl; ineqs = new_ineqs}


  (* This function doesn't check whether incoming ine is already a member of the linear cone. Could consider an alternative*)
  let add_ineq c is_strict ine : (cone * int list) = 
    Log.log_s ~level:`debug "Adding ineq: ";
    Log.log ~level:`debug (pp ~ord:(Cl.get_ord c.closure)) (Some ine);
    Log.log_line_s ~level:`debug "To cone: ";
    Log.log ~level:`debug ppc (Some c);
    let mult_and_minimize_ineqs ineqs available_id ins_to_add = 
      let outer_folder _ ine (n_id, acc) = 
        let inner_folder _ existing_ine (next_id, acc_p) = 
          if existing_ine.d + ine.d <= c.depth then
            (let new_ine, _ = Cl.reduce (mul (dim_to_poly existing_ine.dm) (dim_to_poly ine.dm)) c.closure in
            let new_is_strict = ine.is_strict && existing_ine.is_strict in
            match is_const new_ine with
            | Some cons when C.cmp cons C.zero > 0 -> next_id, acc_p
            | Some cons when C.cmp cons C.zero = 0 && (not new_is_strict) -> next_id, acc_p
            | Some _ -> failwith "Trying to add negative constant to cone"
            | None ->
              let new_in = {dm = poly_to_dim new_ine; d = existing_ine.d + ine.d; prod = List.sort (Int.compare) (existing_ine.prod @ ine.prod); is_strict = new_is_strict} in
              next_id + 1, IM.add next_id new_in acc_p
            )
          else next_id, acc_p
        in
        IM.fold inner_folder ineqs (n_id, acc)
      in
      let next_id, new_prods = IM.fold outer_folder ins_to_add (available_id, IM.empty) in
      let unioner _ _ _ = failwith "Merging maps with duplicate ids" in
      next_id, IM.union unioner ineqs (IM.union unioner ins_to_add new_prods) 
    in
    let poly_id = c.curr_poly in
      let rec make_depth_prod (prev_ineq, prev_dep, prev_prod, id) acc = 
        let curr_depth = prev_dep + 1 in
         if curr_depth <= c.depth then 
          let curr_ineq, _ = Cl.reduce (mul prev_ineq ine) c.closure in
          match is_const curr_ineq with
          | Some cons when C.cmp cons C.zero > 0 -> make_depth_prod (curr_ineq, curr_depth, poly_id :: prev_prod, id) acc
          | Some cons when C.cmp cons C.zero = 0 && (not is_strict) -> make_depth_prod (curr_ineq, curr_depth, poly_id :: prev_prod, id) acc
          | Some _ -> failwith "Trying to add negative constant to cone"
          | None ->
            let ine = {dm = poly_to_dim curr_ineq; d = curr_depth; prod = poly_id :: prev_prod; is_strict} in
            make_depth_prod (curr_ineq, curr_depth, poly_id :: prev_prod, id + 1) (IM.add id ine acc)
        else
          id, acc
      in
      let next_free_id, self_prod = make_depth_prod (from_const C.one, 0, [], poly_id) IM.empty in
      let next_available_id, ineqs = mult_and_minimize_ineqs c.ineqs next_free_id self_prod in
      let new_c = {c with curr_poly = next_available_id; ineqs} in
      Log.log_line_s ~level:`debug "Resulting cone: ";
      Log.log ~level:`debug ppc (Some new_c);
      new_c, List.init (next_available_id - poly_id) (fun i -> poly_id + i)


  module P = Polyhedron.Make(C)(struct
    type v = monic_mon

    let of_string s = 
      try id_to_mon (int_of_string s)
      with Failure _ -> failwith ("can't convert string to mon")

    let fresh_var i = id_to_mon (fresh_dim i)

    let to_string i = string_of_int (mon_to_id i)

    let equal = (=)

    let compare a b = Int.compare (mon_to_id a) (mon_to_id b)

    let hash x = mon_to_id x

    let of_int x = id_to_mon x

    let pp f v = 
      Format.pp_open_hbox f ();
      (try ppmm f v
      with Failure _ -> Format.pp_close_box f (); Format.pp_print_string f ("v." ^ (to_string v)));
      Format.pp_close_box f ()

    module S = MS

    module M = MM

  end
  )

  open Sigs.Form

  let const_dim = snd (make_mon_from_coef (C.zero))

  let extract_const coef_map = 
    try 
      let const = MM.find const_dim coef_map in
      (MM.remove const_dim coef_map, const)
    with Not_found -> coef_map, C.zero

  let saturate (c : cone) (form : poly form) =
    let atoms = Sigs.Form.get_atoms form in
    let reduce_atoms con atos : P.lterm form list  = List.map (map (fun e -> extract_const (poly_to_dim (fst (Cl.reduce e con.closure))))) atos in
    let reduce_form con f : P.lterm form = map (fun e -> extract_const (poly_to_dim (fst (Cl.reduce e con.closure)))) f in

    let rec form_to_z3 con f = 
      match f with
      | Ge e -> P.cntsr_to_z3 `ge con.z3ctx e
      | Gt e -> P.cntsr_to_z3 `gt con.z3ctx e
      | Eq e -> P.cntsr_to_z3 `eq con.z3ctx e
      | Or list -> Z3.Boolean.mk_or con.z3ctx (List.map (form_to_z3 con) list)
      | And list -> Z3.Boolean.mk_and con.z3ctx (List.map (form_to_z3 con) list)
    in
    let eqs_extract = List.map (extract_const % poly_to_dim) (Cl.get_generators c.closure) in
    let non_strict_with_ids, strict_with_ids = 
      IM.fold (fun id i (ns, str) -> if i.is_strict then ns, (id, extract_const i.dm) :: str
                                     else (id, extract_const i.dm) :: ns, str) c.ineqs ([], []) in
    let z3_cnstrs = (List.map (P.cntsr_to_z3 `eq c.z3ctx) eqs_extract) @ 
                    (List.map (P.cntsr_to_z3 `ge c.z3ctx % snd) non_strict_with_ids) @
                    (List.map (P.cntsr_to_z3 `gt c.z3ctx % snd) strict_with_ids)
                     in
    let solver = Z3.Solver.mk_simple_solver c.z3ctx in
    Z3.Solver.add solver z3_cnstrs;
    let reduced_atoms = reduce_atoms c atoms in
    let init_form = form_to_z3 c (reduce_form c form) in
    let (ineqs_to_upgrade, new_eqs, new_ineqs, new_strict) = 
      P.saturate_c c.z3ctx solver eqs_extract (List.map snd non_strict_with_ids) (List.map snd strict_with_ids) init_form reduced_atoms
      in
    Log.log_line_s ~level:`debug ("Found " ^ (string_of_int (List.length (new_eqs @ new_ineqs @ new_strict))) ^ " new consequences");
    Log.log_line_s ~level:`debug ("Found " ^ (string_of_int (List.length ineqs_to_upgrade)) ^ " new equations");
    let rec fixpoint ine_with_ids is_to_up eqs_to_add non_strict_to_add strict_to_add co = 
      if is_to_up = [] && eqs_to_add = [] && non_strict_to_add = [] && strict_to_add = [] then co
      else
        let ids_to_upgrade = List.map (fun index -> fst (List.nth ine_with_ids index)) is_to_up in
        let lterm_to_poly (map, const) = 
          dim_to_poly 
            (if C.cmp const C.zero = 0 then map
            else MM.add const_dim const map)
        in
        let upgraded_cone, modified_ineqs = upgrade_ineqs co ids_to_upgrade (List.map lterm_to_poly eqs_to_add) in

        let add_ineq_to_cone is_strict (con, unadded_ineqs) lterm =
          let ineq_poly = lterm_to_poly lterm in
          let new_c, added = add_ineq con is_strict ineq_poly in 
          let (_, non_lin) = match added with | [] -> 0, [] | x :: xs -> x, xs in
          (new_c, non_lin @ unadded_ineqs)
        in
        let added_ineq_cone, added = List.fold_left (add_ineq_to_cone true) (List.fold_left (add_ineq_to_cone false) (upgraded_cone, []) non_strict_to_add) strict_to_add in
        let to_z3_cnstr id = 
          let ineq = IM.find id added_ineq_cone.ineqs in
          if ineq.is_strict then P.cntsr_to_z3 `gt added_ineq_cone.z3ctx (extract_const ineq.dm)
          else P.cntsr_to_z3 `ge added_ineq_cone.z3ctx (extract_const ineq.dm)
        in
        let new_z3_cnstrs = List.map to_z3_cnstr (added @ modified_ineqs) in
        Z3.Solver.add solver new_z3_cnstrs;
        let curr_generators = List.map (extract_const % poly_to_dim) (Cl.get_generators added_ineq_cone.closure) in
        let curr_non_strict_with_ids, curr_strict_with_ids = 
          IM.fold (fun id i (ns, str) -> if i.is_strict then ns, (id, extract_const i.dm) :: str
                                         else (id, extract_const i.dm) :: ns, str) added_ineq_cone.ineqs ([], []) in
        Z3.Solver.add solver (List.map (P.cntsr_to_z3 `eq added_ineq_cone.z3ctx) curr_generators);
        let new_red_atoms = reduce_atoms added_ineq_cone atoms in
        let next_form = form_to_z3 added_ineq_cone (reduce_form added_ineq_cone form) in
        Log.log_line_s ~level:`debug "Curr cone";
        Log.log ppc ~level:`debug (Some added_ineq_cone);
        let (next_is_to_up, next_new_eqs, next_new_ineqs, next_new_strict) = 
          P.saturate_c added_ineq_cone.z3ctx solver curr_generators (List.map snd curr_non_strict_with_ids) (List.map snd curr_strict_with_ids) next_form new_red_atoms
          in
        Log.log_line_s ~level:`debug ("Found " ^ (string_of_int (List.length next_new_ineqs)) ^ " new consequences");
        Log.log_line_s ~level:`debug ("Found " ^ (string_of_int (List.length next_is_to_up)) ^ " new equations");
        fixpoint curr_non_strict_with_ids next_is_to_up next_new_eqs next_new_ineqs next_new_strict added_ineq_cone
    in
    fixpoint non_strict_with_ids ineqs_to_upgrade new_eqs new_ineqs new_strict c


  (*let saturate (c : cone) (impls : impl list) =
    let impls_red = 
      List.map 
        (fun (h, cons) -> (fst (Cl.reduce h c.closure), fst (Cl.reduce cons c.closure))) impls
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
    let curr_ineqs = BatList.of_enum (BatEnum.map (fun (_, _, (i, _)) -> dim_map_to_z3_ineq i) (BatIMap.enum c.ineqs)) in
    let curr_eqs = List.map (dim_map_to_z3_eq  % poly_to_dim) (Cl.get_generators c.closure) in
    Z3.Solver.add solver (curr_eqs @ curr_ineqs);
    let z3_impls = List.map (fun (h, cons) -> dim_map_to_z3_ineq (poly_to_dim h), dim_map_to_z3_ineq (poly_to_dim cons)) impls_red in

    
    (*Printf.fprintf (open_out "init_cone.smt2") "%s" (Z3.Expr.to_string projected_form);*)
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
        find_all_cons (List.concat (new_pot_eqs :: List.map snd new_pot_cons)) cons_not_in_play_this_round (curr_num + List.length cons_in_play) (fst (upgrade_ineqs temp_cone found_eqs))
    in
    find_all_cons (pot_eqs @ pot_ineqs) [] 0 c*)


  (*let preprocess_ineqs p c = 
    let (_, lm) = lt (make_sorted_poly (Cl.get_ord c.closure) p) in
    let const_dim = mon_to_id (snd (make_mon_from_coef (C.zero))) in
    let folder id (ineq, _) (consts, parity_map) = 
      let ineq_list = List.sort (fun i j -> (-1) * ((Cl.get_ord c.closure) (id_to_mon i) (id_to_mon j))) (BatList.of_enum (IM.keys ineq)) in
      if List.length ineq_list = 0 then (id :: consts, parity_map)
      else if List.length ineq_list = 1 && const_dim = List.hd ineq_list then 
        let dim_coef = IM.find (List.hd ineq_list) ineq in
        if C.cmp dim_coef C.zero < 0 then failwith "Negative const in polyhedron"
        else (id :: consts, parity_map)
      else
        let bigger_mons = List.filter (fun i -> (Cl.get_ord c.closure) (id_to_mon i) lm > 0) ineq_list in
        let update_map map dim = 
          if IM.mem dim map then
            (match IM.find dim map with
            | None -> map
            | Some par -> 
              let dim_coef = IM.find dim ineq in
              if C.cmp dim_coef C.zero = 0 then failwith "ineq has 0 coeficient";
              let dim_par = if C.cmp dim_coef C.zero > 0 then 1 else (-1) in
              if par = dim_par then map
              else IM.modify dim (fun _ -> None) map)
          else
            let dim_coef = IM.find dim ineq in
            if C.cmp dim_coef C.zero = 0 then failwith "ineq has 0 coeficient";
            let dim_par = if C.cmp dim_coef C.zero > 0 then 1 else (-1) in
            IM.add dim (Some dim_par) map
        in
        (consts, List.fold_left update_map parity_map bigger_mons)
    in
    let (const_ineqs, parity_map) = IM.fold folder c.ineqs ([], IM.empty) in
    let collect_irrelevant_dims dim par irrelevant_dims =
      match par with
      | None -> irrelevant_dims
      | Some _ -> dim :: irrelevant_dims
    in
    let irrelevant_dims = IM.fold collect_irrelevant_dims parity_map [] in
    let find_ineq_to_remove id (ineq, _) ineqs_to_remove = 
      if List.exists (fun dim -> IM.mem dim ineq) irrelevant_dims then id :: ineqs_to_remove
      else ineqs_to_remove
    in
    let ineqs_to_remove = IM.fold find_ineq_to_remove c.ineqs const_ineqs in
    Log.log_line_s ~level:`trace ("Preprocessing removed " ^ (string_of_int (List.length ineqs_to_remove)) ^ " ineqs");
    List.fold_left (fun map id_to_remove-> IM.remove id_to_remove map) c.ineqs ineqs_to_remove*)

  (*let reduce_ineq p c = 
    match is_const p with
    | Some _ -> [], p
    | None ->
      let preprocessed_ineqs = preprocess_ineqs p c in
      let ids = BatList.of_enum (IM.keys preprocessed_ineqs) in
      if List.length ids = 0 then [], p
      else 
        let solver = Z3.Optimize.mk_opt c.z3ctx in
        let folder id (ineq, _) (dim_sum_map, ls, ids) = 
          let lambda = Z3.Arithmetic.Real.mk_const_s c.z3ctx ("lambda" ^ (string_of_int id)) in
          let collect_ineq_dims dim coef map = 
            IM.modify_opt dim
              (fun old_e ->
                match old_e with
                | None -> Some (Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef))])
                | Some e -> Some (Z3.Arithmetic.mk_add c.z3ctx [e; Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c coef))]])
              ) map
          in
          Z3.Optimize.add solver [Z3.Arithmetic.mk_le c.z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)];
          IM.fold collect_ineq_dims ineq dim_sum_map, lambda :: ls, id :: ids
        in
        let dim_sum_map, lambdas, ids = IM.fold folder preprocessed_ineqs (IM.empty, [], []) in
        Log.log_line_s ~level:`trace (string_of_int (IM.cardinal dim_sum_map) ^ " dimensions");
        Log.log_line_s ~level:`trace ((string_of_int (List.length lambdas)) ^ " ineqs");
        let p_dim_map = poly_to_dim p in
        let dims_sorted_small_to_big = 
          List.sort (fun i_dim j_dim -> (Cl.get_ord c.closure) (id_to_mon i_dim) (id_to_mon j_dim)) 
            (BatList.of_enum (BatEnum.uniq (BatEnum.append (IM.keys dim_sum_map) (IM.keys p_dim_map)))) in
        let dims_and_r_cons = List.map
          (fun dim -> 
            let r = Z3.Arithmetic.Real.mk_const_s c.z3ctx ("r" ^ (string_of_int dim)) in
            if IM.mem dim p_dim_map && IM.mem dim dim_sum_map then
              (let p_coef = IM.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c p_coef)) (Z3.Arithmetic.mk_add c.z3ctx [r; IM.find dim dim_sum_map])]; (* p_c = sum lambda_i + r *)
              (dim, r))
            else if IM.mem dim p_dim_map then
              (let p_coef = IM.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (C.to_string_c p_coef)) r]; (* p_c = r*)
              (dim, r))
            else
              (Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0) (Z3.Arithmetic.mk_add c.z3ctx [r; IM.find dim dim_sum_map])]; (* 0 = sum lambda_i + r*)
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
            let collect_lambdas neg_comb (lambda, ineq_id) = 
              match (Z3.Model.get_const_interp_e model lambda) with
              | None -> failwith "Z3 model doesn't have a lambda"
              | Some lc ->
                let lambdac = C.of_zarith_q (Z3.Arithmetic.Real.get_ratio lc) in
                if C.cmp lambdac (C.from_string_c "0") = 0 then neg_comb
                else
                  (lambdac, ineq_id) :: neg_comb
            in
            let neg_comb = List.fold_left collect_lambdas [] (List.combine lambdas ids) in
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
            neg_comb, rem*)
        
  (*let reduce_eq p c = Cl.reduce p c.closure*)

  (*let pp_eqred ord f (p, basis, mults, rem) = 
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
    Format.pp_close_box f (); Format.pp_close_box f ())

  let pp_red f (p, neg_comb, rem, c) =
    Format.pp_open_hbox f (); Format.pp_print_string f "Theorem "; Format.pp_print_string f ":";
    pp ~ord:(Cl.get_ord c.closure) f p; Format.pp_print_string f " <= "; pp ~ord:(Cl.get_ord c.closure) f rem; Format.pp_close_box f (); Format.pp_force_newline f ();
    Format.pp_open_box f 0; Format.pp_print_string f "Proof:"; Format.pp_open_vbox f 0; Format.pp_print_space f ();
    Format.pp_open_vbox f 0;
    let ineqs_used, ineq_mults = List.split (List.map (fun (coe, id) -> dim_to_poly (fst (IM.find id c.ineqs)), from_const coe) neg_comb) in 
    pp_eqred (Cl.get_ord c.closure) f (p, ineqs_used, ineq_mults, rem);
    Format.pp_force_newline f ();
    Format.pp_print_string f "QED";
    Format.pp_force_newline f ();
    Format.pp_close_box f ()*)

  let pp_stats f c = 
    let num_eqs = Cl.get_num_eqs c.closure in
    let ineqs = BatList.of_enum (BatEnum.map (fun a -> a.dm) (IM.values c.ineqs)) in
    let num_ineqs = List.length ineqs in
    let mons = List.fold_left (fun acc ine -> MS.union acc (MM.domain ine)) MS.empty ineqs in
    let num_mons = MS.cardinal mons in
    Format.pp_print_string f "Cone size: ";
    Format.pp_open_vbox f 0;
    Format.pp_print_string f "Num eqs: "; Format.pp_print_int f num_eqs; Format.pp_print_space f ();
    Format.pp_print_string f "Num ineqs: "; Format.pp_print_int f num_ineqs; Format.pp_print_space f ();
    Format.pp_print_string f "Num of unique mons in ineqs: "; Format.pp_print_int f num_mons; Format.pp_close_box f ()


  let i_reduce_ineq use_proj p c = 
    let bigD = id_to_mon (fresh_dim ()) in
    let ineqs = c.ineqs in
    let p_ired_m = extract_const (poly_to_dim p) in
    let all_dims = IM.fold (fun _ ine dim_set -> MS.union (MM.domain ine.dm) dim_set) ineqs MS.empty in
    let sorted_dims = List.rev (List.sort (fun i j -> Cl.get_ord c.closure i j) (MS.to_list all_dims)) in
    let solver = Z3.Solver.mk_simple_solver c.z3ctx in
    let ineqs_ex = IM.fold (fun _ ine ineqs -> extract_const ine.dm :: ineqs) ineqs [] in
    let z3_ineqs = List.map (P.cntsr_to_z3 `ge c.z3ctx) ineqs_ex in
    let polyhedron = List.fold_left (P.add_cnstr `ge) P.top_p ineqs_ex in
    Z3.Solver.add solver z3_ineqs;
    let (uppers, lowers) = P.optimize_t ~use_proj:use_proj p_ired_m bigD sorted_dims polyhedron c.z3ctx solver in
    let bounds_to_polys c = dim_to_poly (MM.add const_dim (snd c) (fst c)) in
    List.map bounds_to_polys uppers, List.map bounds_to_polys lowers
     


  let reduce ?(use_proj = true) p c = 
    let p_ired,_ = Cl.reduce p c.closure in
    (*let neg_comb, p_ineq_red = Log.log_time_cum "reduce ineq" (reduce_ineq p_ired) c in
    (*let eq_just = {orig = p_ired; mults} in*)
    Log.log ~level:`debug pp_red (Some (p_ired, neg_comb, p_ineq_red, c));*)
    Log.log ~level:`debug pp_stats (Some c);
    let pp_ups f ups = 
      let pp_up fo up = 
        pp ~ord:(Cl.get_ord c.closure) fo p; Format.pp_print_string fo " <= "; pp ~ord:(Cl.get_ord c.closure) fo up
      in
      Format.pp_open_vbox f 0;
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) pp_up f ups;
      Format.pp_close_box f ()
    in
    let pp_lows f lows = 
      let pp_low fo low = 
        pp ~ord:(Cl.get_ord c.closure) fo p; Format.pp_print_string fo " >= "; pp ~ord:(Cl.get_ord c.closure) fo low
      in
      Format.pp_open_vbox f 0;
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) pp_low f lows;
      Format.pp_close_box f ()
    in
    let ups, lows = i_reduce_ineq use_proj p_ired c in
    Log.log_line_s ~level:`trace "Reduced polys: ";
    Log.log ~level:`trace pp_ups (Some ups);
    Log.log ~level:`trace pp_lows (Some lows);
    ups, lows

    (*p_ineq_red*)
    

  
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

  let impl_to_form (h, tl) = 
    Sigs.Form.Or [Sigs.Form.Gt (negate h); Sigs.Form.Ge tl]

  let make_cone_cl ?(sat = 1) ?(ineqs = []) ?(impls = [])  cl = 
    let ineqs = ineqs @ (Cl.instantiate_ineqs cl) in
    let impls = impls @ (Cl.instantiate_impls cl) in
    let red_add_ine co ine = fst (add_ineq co false ine) in
    let prod_sat_cone = 
      List.fold_left red_add_ine (make_empty_cone sat cl) ineqs in
    let unnormal_c = saturate prod_sat_cone (Sigs.Form.And (List.map impl_to_form impls)) in
    (*Log.log_time_cum "normalize" normalize unnormal_c*)
    unnormal_c
  
  let make_cone_cl_form ?(sat = 1) ?(ineqs = []) form cl =
    let ineqs = ineqs @ (Cl.instantiate_ineqs cl) in
    let impls = Cl.instantiate_impls cl in
    let red_add_ine co ine = fst (add_ineq co false ine) in
    let prod_sat_cone = 
      List.fold_left red_add_ine (make_empty_cone sat cl) ineqs in
    let unnormal_c = saturate prod_sat_cone (Sigs.Form.And (form :: (List.map impl_to_form impls))) in
    (*Log.log_time_cum "normalize" normalize unnormal_c*)
    unnormal_c
    

  let unpurify p con = Cl.unpurify p con.closure


  let set_effective_degree c vars_to_keep = 
    let cl = Cl.set_effective_degree c.closure vars_to_keep in
    fst (reduce_ineqs {c with closure = cl})

  
end