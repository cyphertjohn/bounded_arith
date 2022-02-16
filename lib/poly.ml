module type Polynomial = sig
  type monic_mon

  type coef

  type mon = coef * monic_mon

  type poly

  val get_mons : poly -> mon BatEnum.t

  val get_degree : string -> monic_mon -> int

  val get_vars_m : monic_mon -> string BatEnum.t

  val add :
    poly -> poly -> poly

  val addi :
    poly -> poly -> unit


  val mul :
    poly -> poly -> poly
    
  val exp_poly : poly -> int -> poly

  val substitute :
    string * poly -> poly -> poly

  val is_zero : poly -> bool

  val is_const : poly -> bool

  val compare : poly -> poly -> int

  val equal : poly -> poly -> bool
    
  val from_string : string -> poly

  val from_var : string -> poly

  val from_const_s : string -> poly

  val from_var_pow : string -> int -> poly

  val negate : poly -> poly

  val to_string : poly -> string

  val get_vars : poly -> string BatEnum.t

  val from_const : coef -> poly

  (*val normalize : poly -> poly*)
end

let (%) = BatPervasives.(%)

module Make (C : Sigs.Coefficient) = struct

  module PP = PrePoly.Make(C)

  module P = PolyParse.Make(PP)


  let from_string s = (P.main PolyLexer.token (Lexing.from_string s))


  include PP

  type monic_mon = Mon.monic_mon

  type mon = C.coef * monic_mon

  type coef = C.coef

end

module PQ = Make(Sigs.Q)


module type Ideal = sig 

    type ideal

    type poly

    type monic_mon

    val make_ideal : (monic_mon -> monic_mon -> int) -> poly list -> ideal

    val make_ideal_f : int BatMap.String.t -> bool BatMap.String.t -> (int * string) list -> poly list -> ideal

    val mem : poly -> ideal -> bool

    val reduce : poly -> ideal -> poly

    val get_generators : ideal -> poly list

    val ppi : Format.formatter -> ideal -> unit

    val equal : ideal -> ideal -> bool

end

module Ideal (C : Sigs.Coefficient) = struct

  include Make(C)

  type sorted_poly = poly * Mon.monic_mon list

  type generators = 
    | Top (*<1>*)
    | Bot (*<0>*)
    | I of sorted_poly list (*<p1,...,pn>*)

  type ideal = {
    basis: generators;
    ord: Mon.monic_mon -> Mon.monic_mon -> int
  }

  (*let ppsp f (sp : sorted_poly) =
    let folder (acc, first) (is_neg, m_s) =
      if first && is_neg then "-" ^ m_s, false
      else if first then m_s, false
      else if is_neg then acc ^ " - " ^ m_s, false
      else acc ^ " + " ^ m_s, false
    in
    let sorted_mon_list = List.map (fun m -> (BatHashtbl.find (fst sp) m), m) (snd sp) in
    let str = fst (List.fold_left folder ("", true) (List.map Mon.mon_to_string sorted_mon_list)) in
    Format.pp_print_string f (str ^ "\n")*)
    

  let make_sorted_poly ord p : sorted_poly = 
    let pc = BatHashtbl.copy p in
    let monics = BatEnum.map snd (get_mons pc) in
    let sorted_monics = List.rev (List.sort ord (BatList.of_enum monics)) in
    (pc, sorted_monics)

  

  let lt ((p, mons) : sorted_poly) = 
    if List.length mons = 0 then Mon.zero
    else 
      match BatHashtbl.find_option p (List.hd mons) with
      | Some c -> c, List.hd mons
      | None ->
        Log.log_line_s ~level:`trace "Found a mon not in tbl";
        BatHashtbl.find p (List.hd mons), (List.hd mons)

  let lc p = fst (lt p)

  let division ord divisors f =
    let find_map func lis = 
      let rec foo l i =
        match l with
        | [] -> None
        | x :: xs ->
          match func x with 
          | None -> foo xs (i+1)
          | Some y -> Some (y, i)
      in
      foo lis 0
    in
    let reduction_occurred = ref false in
    let rec aux p mults (r : sorted_poly) = 
      if is_zero (fst p) then (mults, r)
      else 
        let ltp = lt p in
        let ltdiv fi = Mon.divide_mon ltp (lt fi) in
        match find_map ltdiv divisors with
        | None ->
          subtract_mon (fst p) ltp;
          let new_pmons = List.tl (snd p) in
          add_mon (fst r) ltp;
          aux (fst p, new_pmons) mults (fst r, (snd r) @ [snd ltp])
        | Some (new_mon, i) ->
          reduction_occurred := true;
          subtract (fst p) (mult_mon_poly new_mon (fst (List.nth divisors i)));
          List.iteri (fun j x -> if j = i then add_mon x new_mon) mults;
          aux (make_sorted_poly ord (fst p)) mults r
    in
    (!reduction_occurred, aux f (List.map (fun _ -> (make_poly_from_mon Mon.zero)) divisors) ((make_poly_from_mon Mon.zero), []))

  let s_poly ord f g =
    let lcmlm = (Mon.from_string_c "1", Mon.lcm_of_mon (snd (lt f)) (snd (lt g))) in
    let f_m = Mon.divide_mon lcmlm (lt f) in
    let g_m = Mon.divide_mon lcmlm (lt g) in
    match (f_m, g_m) with
    | (Some f_t, Some g_t) ->
      let ftf = mult_mon_poly f_t (fst f) in
      subtract ftf (mult_mon_poly g_t (fst g));
      make_sorted_poly ord ftf
    | _ -> failwith "shouldn't happen"


  let minimize fs = 
    let monic_grobner = List.map 
      (fun poly -> 
        let lc = lc poly in
        BatHashtbl.map_inplace (fun _ c -> Mon.divc c lc) (fst poly);
        (fst poly), snd poly
      ) fs in
    let is_need poly l = 
      let divides x = match Mon.divide_mon (lt poly) (lt x) with | Some _ -> true | None -> false in
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
    else if List.exists (fun (p, _) -> is_const p) min_basis then
      Top
    else
      I min_basis

  let improved_buchberger ord fs = 
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
              match Mon.divide_mon (lt (List.nth g k)) lcmu with
              | None -> foo (k+1)
              | Some _ -> true
        in
        foo 0
      in
      match worklist with
      | [] -> 
        {basis = minimize g; ord}
      | (i, j) :: rest ->
        let (fi, fj) = (List.nth g i, List.nth g j) in
        let lcmlt = Mon.lcm_of_mon (snd (lt fi)) (snd (lt fj)) in (* lt or lm? *)
        let prod = (Mon.mult_mon (lt fi) (lt fj)) in
        if criterion i j (Mon.from_string_c "1", lcmlt) then aux rest g
        else if Mon.lex_ord lcmlt (snd prod) = 0 then aux rest g (* criterion *)
        else (
          let sp = s_poly ord fi fj in
          let (_, (_, s)) = division ord g sp in
          if is_zero (fst s) then aux rest g
          else if is_const (fst s) then {basis=Top; ord}
          else 
            aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) g)) (g @ [s])
        )
    in
    let norm_fs = List.map (make_sorted_poly ord) (List.rev (List.sort compare fs)) in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
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
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ","; Format.pp_print_space fo ()) (pp ~ord:i.ord) f (List.map fst basis);
        Format.pp_print_string f ">";
        Format.pp_close_box f ());
    Format.pp_close_box f ()


  let pp_red ord f (p, basis, mults, rem) = 
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

  let reduce p (i : ideal) : poly = 
    match i.basis with
    | Top ->
      from_const_s "0"
    | Bot -> p
    | I basis -> 
      let (_, (_, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      (*let (reduction_occurred, (mults, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      if not reduction_occurred then Log.log ~level:`trace (pp_red i.ord) None
      else Log.log ~level:`trace (pp_red i.ord) (Some (p, List.map fst basis, mults, fst rem));*)
      fst rem

  let reduce_just p (i : ideal) =
    match i.basis with
    | Top -> from_const_s "0", [from_const_s "1"]
    | Bot -> p, [from_const_s "0"]
    | I basis ->
      let (_, (mults, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      fst rem, mults


  let make_ideal ord eqs : ideal = 
    let normal = List.filter (not % is_zero) eqs in
    if List.length normal = 0 || List.for_all is_zero normal then 
      {basis = Bot; ord}
    else if List.exists is_const normal then 
      {basis = Top; ord}
    else 
      improved_buchberger ord normal
     

  let make_grevlex_from_list deg_map bk1 bk2 m1 m2 = 
    let effective_deg v = match BatMap.String.find_opt v deg_map with None -> 1 | Some e -> e in
    let m1d_bk_1 = List.map (fun v -> effective_deg v * Mon.degree v m1) bk1 in
    let m2d_bk_1 = List.map (fun v -> effective_deg v * Mon.degree v m2) bk1 in
    let m1bk1tot, m2bk1tot = List.fold_left (+) 0 m1d_bk_1, List.fold_left (+) 0 m2d_bk_1 in
    if m1bk1tot = m2bk1tot then
      let grevlex_bk1 = 
        try (List.find ((<>) 0) (List.rev (List.map2 (-) m1d_bk_1 m2d_bk_1)))
        with Not_found -> 0 in
      if grevlex_bk1 <> 0 then (-1) * grevlex_bk1
      else
        let m1d_bk_2 = List.map (fun v -> effective_deg v * Mon.degree v m1) bk2 in
        let m2d_bk_2 = List.map (fun v -> effective_deg v * Mon.degree v m2) bk2 in
        let m1bk2tot, m2bk2tot = List.fold_left (+) 0 m1d_bk_2, List.fold_left (+) 0 m2d_bk_2 in
        if m1bk2tot = m2bk2tot then
          try (-1) * (List.find ((<>) 0) (List.rev (List.map2 (-) m1d_bk_2 m2d_bk_2)))
          with Not_found -> 0
        else Int.compare m1bk2tot m2bk2tot
    else
      Int.compare m1bk1tot m2bk1tot

  let convert_to_faugere l (p : poly) = 
    let clearing_denom = 
      BatHashtbl.fold (fun _ c acc  -> Z.lcm (Q.den (Mon.to_zarith c)) acc) p Z.one in
    let mon_to_faugere (m, c) = 
      let md = List.map (fun v -> Mon.degree v m) l in
      let new_c = Q.num (Q.mul (Mon.to_zarith c) (Q.of_bigint clearing_denom)) in
      new_c, md
    in
    List.map mon_to_faugere (BatHashtbl.to_list p)

  let convert_from_faugere l p = 
    from_mon_list (List.map (Mon.make_mon_from_faugere_mon l) p)

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
    Format.pp_close_box f ()*)

  let curr_var = ref 0

  let new_var () = 
    let y = "y_"^ (string_of_int !curr_var) in
    curr_var := !curr_var + 1;
    y
  
  let effective_deg_ord_as_list deg_map keep_map top_order ps = 
    let vars = BatMap.String.keys keep_map in
    let (keep_vars, discard_vars) = BatEnum.partition (fun v -> BatMap.String.find v keep_map) vars in
    let cmp_var x y =
      match (List.find_opt (fun (_, v) -> v = x) top_order, List.find_opt (fun (_, v) -> v = y) top_order) with
      | None, None -> (-1) *(String.compare x y)
      | Some (_, _), None -> 1
      | None, Some (_, _) -> (-1)
      | Some (x_ind, _), Some (y_ind, _) ->
        Int.compare x_ind y_ind
    in
    let var_ord_bk_1, var_ord_bk_2 = (List.rev (List.sort cmp_var (BatList.of_enum discard_vars))), (List.rev (List.sort cmp_var (BatList.of_enum keep_vars))) in
    let folder (svar_ord, svar_to_pvar_e, polys) pvar = 
      let pedeg = match BatMap.String.find_opt pvar deg_map with | None -> 1 | Some e -> e in
      let svar = new_var () in
      let svar_edeg = from_var_pow svar pedeg in
      let sub_ps = List.map (substitute (pvar, svar_edeg)) polys in
      svar :: svar_ord, BatMap.String.add svar (pvar, pedeg) svar_to_pvar_e, sub_ps
    in
    let rord_bk_1, svar_to_pvar, subps = List.fold_left folder ([], BatMap.String.empty, ps) var_ord_bk_1 in
    let rord_bk_2, svar_to_pvar, subps = List.fold_left folder ([], svar_to_pvar, subps) var_ord_bk_2 in
    ((var_ord_bk_1, var_ord_bk_2), (List.rev rord_bk_1, List.rev rord_bk_2), svar_to_pvar, subps)


  let make_ideal_f deg_map keep_map top_ord eqs : ideal = 
    let normal = List.filter (fun p -> not (is_zero p)) eqs in
    let ((orig_vord_bk1, orig_vord_bk2), (vord_bk1, vord_bk2), svar_to_pvar, subps) = effective_deg_ord_as_list deg_map keep_map top_ord normal in
    let ord = make_grevlex_from_list deg_map orig_vord_bk1 orig_vord_bk2 in
    if List.length normal = 0 || List.for_all is_zero normal then 
      {basis = Bot; ord}
    else if List.exists is_const normal then 
      {basis = Top; ord}
    else 
      let fpolys = List.map (convert_to_faugere (vord_bk1 @ vord_bk2)) subps in
      let gb = List.map (convert_from_faugere (vord_bk1 @ vord_bk2)) (Faugere_zarith.Fgb_int_zarith.fgb fpolys vord_bk1 vord_bk2) in
      let mon_sub m = 
        let c, monic = fst m, snd m in 
        let folder acc v = 
          let vdeg = get_degree v monic in
          let (old_var, eff_deg) = BatMap.String.find v svar_to_pvar in
          if vdeg mod eff_deg = 0 then 
            let new_deg = vdeg / eff_deg in
            Mon.mult_mon (Mon.make_mon_from_var old_var new_deg) acc
          else failwith "Not sure how to do this subtitution"
        in
        BatEnum.fold folder (Mon.make_mon_from_coef c) (get_vars_m monic)
      in
      let poly_sub p = 
        let mons = get_mons p in
        from_mon_list (BatList.of_enum (BatEnum.map mon_sub mons))
      in
      let normal_gb = List.filter (fun p -> not (is_zero p)) gb in
      if List.length normal_gb = 0 || List.for_all is_zero normal_gb then {basis = Bot; ord}
      else if List.exists is_const normal_gb then {basis = Top; ord}
      else
        let sorted_gb = List.map (fun p -> make_sorted_poly ord (poly_sub p)) normal_gb in
        {basis = I sorted_gb; ord}

  let compare_sorted ord (p1, mon_list1) (p2, mon_list2) = 
    let rec aux ml1 ml2 = 
      match ml1, ml2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | m1 :: m1s, m2 :: m2s ->
        let cmp_res = ord m1 m2 in
        if cmp_res <> 0 then cmp_res
        else
          let m1c, m2c = BatHashtbl.find p1 m1, BatHashtbl.find p2 m2 in
          let coef_cmp = Mon.cmp m1c m2c in
          if coef_cmp <> 0 then coef_cmp
          else aux m1s m2s
    in
    aux mon_list1 mon_list2

  let equal i1 i2 = 
    match i1.basis, i2.basis with
    | Bot, Bot -> true
    | Top, Top -> true
    | I b1, I b2 ->
      if List.length b1 <> List.length b2 then false
      else
        let b1ss, b2ss = List.sort (compare_sorted Mon.lex_ord) b1, List.sort (compare_sorted Mon.lex_ord) b2 in
        let rec eq (p1, p1l) (p2, p2l) = 
          match p1l, p2l with
          | [], [] -> true
          | [], _ -> false
          | _, [] -> false
          | p1m :: p1ls, p2m :: p2ls ->
            if p1m = p2m then 
              let p1c, p2c = BatHashtbl.find p1 p1m, BatHashtbl.find p2 p2m in
              let coef_cmp = Mon.cmp p1c p2c in
              if coef_cmp <> 0 then false
              else eq (p1, p1ls) (p2, p2ls)
            else false
        in
        let eqs = List.map2 eq b1ss b2ss in
        List.for_all (fun x -> x) eqs
    | _ -> false


  let mem p i =
    match i.basis with
    | Top -> true
    | Bot -> false
    | I _ -> is_zero (reduce p i)

  let get_generators (i : ideal) : poly list = 
    match i.basis with
    | Top -> [from_const_s "1"]
    | Bot -> [from_const_s "0"]
    | I basis -> List.map fst basis

end

module type Cone = sig 
    type cone

    type poly

    type ideal

    type monic_mon

    type impl = poly * poly

    val (=>) : poly -> poly -> impl

    val make_cone : ?sat:int -> ?ord:(monic_mon -> monic_mon -> int) -> ?eqs:poly list -> ?ineqs:poly list -> ?impls: impl list -> unit -> cone

    val make_cone_i : ?sat:int -> ?ineqs:poly list -> ?impls:impl list -> ideal -> cone

    (*val is_non_neg : poly -> cone -> bool*)

    val reduce : poly -> cone -> poly

    val reduce_eq : poly -> cone -> poly

    val get_eq_basis : cone -> poly list

    val get_ineq_basis : cone -> poly list
end


module Cone(C : Sigs.Coefficient) = struct
  module I = Ideal(C)
  include I
  
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

  type eqJust = 
    {
      orig : poly;
      mults : poly list
    }
  
  type posCom = PosComb of ((int * coef) list * I.coef)

  type derJust = eqJust * posCom

  type justification = 
   | Product of eqJust * (int list)
   | Given of eqJust * derJust option

  type cone = 
    {
      depth : int;
      ideal : I.ideal;
      curr_num : int;
      ineqs : (poly * justification) BatIMap.t;
      ineqs_prod : int list list list
    }

  (*type cone = int * I.ideal * poly list list*)

  let is_const_not_neg p = 
    if I.is_const p then
      let c = fst (List.hd (BatList.of_enum (I.get_mons p))) in
      if I.Mon.cmp c (I.Mon.from_string_c "0") >= 0 then Some c
      else None
    else None

  (*let saturate_prod l depth = 
    let rec aux1 l1 d =
      if d <= 1 then
        match l1 with
        | [] -> []
        | x :: xs ->
          [x] :: (aux1 xs d)
      else 
        match l1 with 
        | [] -> []
        | x :: [] -> 
          let prev = aux1 l1 (d - 1) in
          (List.map (fun e -> mul x e) (List.hd prev)) :: prev
        | x :: xs ->
          let prev = aux1 xs d in 
          let rec aux2 dyn = 
            match dyn with
            | [] -> []
            | my_level :: rest ->
              let new_dyn = aux2 rest in
              if List.length new_dyn = 0 then [x :: my_level]
              else
                let prev_level = List.hd new_dyn in
                let new_level = (List.map (fun e -> mul x e) prev_level) @ my_level in
                new_level :: new_dyn
          in
          aux2 prev
        in
      List.rev (aux1 l depth)*)

  (* This function doesn't check whether incoming ine is already a member of the linear cone. Could consider an alternative*)
  let add_ineq c ine just : cone = 
    let mult_and_minimize_ineqs (ineqs, curr_id) ins_to_add = 
      let reduce_and_just (inequs, id) prod = 
        let p = List.fold_left (fun acc ind -> I.mul acc (fst (BatIMap.find ind inequs))) (I.from_const_s "1") prod in
        let p_red, mults = I.reduce_just p c.ideal in
        match is_const_not_neg p_red with
        | Some _ -> inequs, id
        | None ->
          let eq_just = {orig = p; mults} in
          let new_ineqs = BatIMap.add id (p_red, Product (eq_just, prod)) inequs in
          new_ineqs, (id + 1)
      in
      List.fold_left reduce_and_just (ineqs, curr_id) ins_to_add
    in
    if not (is_const_not_neg ine = None) then c
    else if BatIMap.is_empty c.ineqs then 
      let poly_id = c.curr_num in
      let rec dup v t = if t <=0 then [] else v :: (dup v (t-1)) in
      let rec aux acc depth = 
        if depth <= 0 then acc
        else 
          aux ([dup poly_id depth] :: acc) (depth - 1)
      in
      let ineq_ladder = aux [] c.depth in
      let prod_to_comput = List.concat (List.tl ineq_ladder) in
      let ineqs, next_id = mult_and_minimize_ineqs ((BatIMap.add poly_id (ine, just) (BatIMap.empty ~eq:(fun _ _ -> false))), poly_id + 1) prod_to_comput in
      {depth = c.depth; ideal = c.ideal; curr_num = next_id; ineqs; ineqs_prod = ineq_ladder}
    else 
      let poly_id = c.curr_num in
      let folder (all_ineq, new_ineqs) curr_level = 
        if List.length all_ineq = 0 then [[poly_id] :: curr_level], new_ineqs
        else
          let prev_level = List.hd all_ineq in
          let new_ineq = List.map (fun p -> poly_id :: p) prev_level in
          (new_ineq @ curr_level) :: all_ineq, new_ineq @ new_ineqs
      in
      let ineqs_with_ine = BatIMap.add poly_id (ine, just) c.ineqs in
      let ineqs_ladder, ineqs_to_add = List.fold_left folder ([], []) c.ineqs_prod in
      let ineqs, next_id = mult_and_minimize_ineqs (ineqs_with_ine, poly_id + 1) ineqs_to_add in
      {depth = c.depth; ideal = c.ideal; curr_num = next_id; ineqs; ineqs_prod = List.rev ineqs_ladder}


  module MonMap = BatHashtbl

  module DimMap = BatIMap

  let polys_to_dim ?ord:(ord = None) p polys = 
    let mon_map = MonMap.create (10 * (BatISet.cardinal (BatIMap.domain polys))) in
    let add_mons _ (poly, _) = 
      BatEnum.iter (fun (_, m) -> MonMap.modify_def 0 m (fun _ -> 0) mon_map) (get_mons poly)
    in
    BatIMap.iter add_mons polys;
    BatEnum.iter (fun (_, m) -> MonMap.modify_def 0 m (fun _ -> 0) mon_map) (get_mons p);
    let mon_list = 
      match ord with
      | None -> BatList.of_enum (BatEnum.map fst (MonMap.enum mon_map))
      | Some o -> List.sort (fun a b ->(-1) * ( o a b)) (BatList.of_enum (BatEnum.map fst (MonMap.enum mon_map)))
    in
    let curr_dim = ref 0 in
    let rec generate_dims mons curr_dim_map = 
      match mons with
      | [] -> curr_dim_map
      | m :: ms ->
        let new_dim_map = DimMap.add !curr_dim m curr_dim_map in
        MonMap.modify m (fun _ -> !curr_dim) mon_map;
        curr_dim := !curr_dim + 1;
        generate_dims ms new_dim_map
    in
    let dim_map = generate_dims mon_list (DimMap.empty ~eq:(=)) in
    let poly_to_coef_map (poly, _) = 
      BatEnum.fold (fun acc (c, mon) -> 
        let dim = MonMap.find mon_map mon in
        DimMap.add dim c acc) (DimMap.empty ~eq:(fun x y -> Mon.cmp x y = 0)) (get_mons poly)
    in
    dim_map, poly_to_coef_map (p, ()), BatIMap.map poly_to_coef_map polys
    
  (*let pp_prob f prob = 
    let prob_str = Lp.Problem.to_string ~short:true prob in
    Format.pp_print_string f prob_str;
    Format.force_newline ()*)


  let is_non_neg p c : derJust option = 
    let id = c.ideal in
    let p_ired, mults = I.reduce_just p id in
    match is_const_not_neg p_ired with
    | Some coe ->
      let eq_just = {orig = p; mults} in
      Some (eq_just, PosComb ([], coe))
    | None ->
      if I.is_const p_ired then None
      else
        let eq_just = {orig = p; mults} in
        let dim_map, p_dim, p_ineq = polys_to_dim ~ord:None p_ired c.ineqs in
        let ids = BatISet.elements (BatIMap.domain p_ineq) in
        let z3ctx = Z3.mk_context [] in
        let solver = Z3.Solver.mk_simple_solver z3ctx in
        let lambdas = List.map (fun id -> (Z3.Arithmetic.Real.mk_const_s z3ctx ("lambda" ^ (string_of_int id)))) ids in
        Z3.Solver.add solver (List.map (fun lambda -> Z3.Arithmetic.mk_ge z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)) lambdas);
        let ineq_dim_lambda = List.combine lambdas ids in
        let generate_cnstrs dim m r_var = 
          let generate_lhs_sum sum (lambda, ineq_id) = 
            try 
              let dim_c = DimMap.find dim (BatIMap.find ineq_id p_ineq) in
              Z3.Arithmetic.mk_add z3ctx [sum; Z3.Arithmetic.mk_mul z3ctx [(Z3.Arithmetic.Real.mk_numeral_s z3ctx (Mon.to_string_c dim_c)); lambda]] 
            with Not_found -> sum
            in
          let sum = List.fold_left generate_lhs_sum (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) ineq_dim_lambda in
          let p_coef = 
            try Z3.Arithmetic.Real.mk_numeral_s z3ctx (Mon.to_string_c (DimMap.find dim p_dim))
            with Not_found -> Z3.Arithmetic.Real.mk_numeral_i z3ctx 0
          in
          if I.Mon.is_const (I.Mon.from_string_c "0", m) then
            let r = Z3.Arithmetic.Real.mk_const_s z3ctx "r" in
            Z3.Solver.add solver [Z3.Arithmetic.mk_ge z3ctx r (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)]; (* r >= 0*)
            Z3.Solver.add solver [Z3.Boolean.mk_eq z3ctx p_coef (Z3.Arithmetic.mk_add z3ctx [sum; r])];   (* p_coef = sum (lambda_i q_i) + r*)
            Some r
          else
            (Z3.Solver.add solver [Z3.Boolean.mk_eq z3ctx p_coef sum]; (* p_coef = sum (lambda_i q_i)*)
            r_var)
        in
      let r_opt = DimMap.fold generate_cnstrs dim_map None in
      let r = match r_opt with | Some v -> v | None -> failwith "no constant constraint was created" in
      match Z3.Solver.check solver [] with
      | Z3.Solver.UNKNOWN | Z3.Solver.UNSATISFIABLE -> None
      | Z3.Solver.SATISFIABLE ->
        match Z3.Solver.get_model solver with
        | None -> failwith "check is sat but no model?"
        | Some model ->
          let collect_lambdas pos_comb (lambda, ineq_id) = 
            match Z3.Model.get_const_interp_e model lambda with
            | None -> failwith "model doesn't have interpretation for a lambda"
            | Some v ->
              let lambdac = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio v) in
              if Mon.cmp lambdac (Mon.from_string_c "0") = 0 then pos_comb
              else
                (ineq_id, lambdac) :: pos_comb
          in
          let pos_comb = List.fold_left collect_lambdas [] ineq_dim_lambda in
          match Z3.Model.get_const_interp_e model r with
          | None -> failwith "model doesn't have interpretation for r"
          | Some rv ->
            let witness = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio rv) in
            Some (eq_just, PosComb (pos_comb, witness))


  let pp_used_th c fo id = 
    Format.pp_print_string fo "Theorem "; Format.pp_print_int fo id; Format.pp_print_string fo ":";
    pp ~ord:c.ideal.ord fo (fst (BatIMap.find id c.ineqs)); Format.pp_print_string fo " >= 0"

  let rec pp_just c f ineq_id = 
    let ineq, just = BatIMap.find ineq_id c.ineqs in
    match just with
    | Given (eq_just, None) ->
      Format.pp_open_hbox f (); Format.pp_print_string f "Theorem "; Format.pp_print_int f ineq_id; Format.pp_print_string f ":";
      pp ~ord:c.ideal.ord f ineq; Format.pp_print_string f " >= 0"; Format.pp_close_box f (); Format.pp_force_newline f ();
      Format.pp_open_box f 0; Format.pp_print_string f "Proof:"; Format.pp_open_vbox f 0; Format.pp_print_space f ();
      Format.pp_open_hbox f (); Format.pp_print_string f "Assumption:"; Format.pp_print_space f (); 
        pp ~ord:c.ideal.ord f eq_just.orig; Format.pp_print_string f " >= 0"; Format.pp_close_box f (); 
      Format.pp_print_space f ();
      pp_red c.ideal.ord f (eq_just.orig, get_generators c.ideal, eq_just.mults, ineq);
      Format.pp_close_box f ();
      Format.pp_print_string f "QED";
      Format.pp_force_newline f ();
      Format.pp_close_box f ()
    | Product (eq_just, prods) ->
      let uniq_ths = BatList.of_enum (BatEnum.uniq (BatList.enum prods)) in
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_force_newline fo ()) (pp_just c) f uniq_ths;
      Format.pp_open_hbox f (); Format.pp_print_string f "Theorem "; Format.pp_print_int f ineq_id; Format.pp_print_string f ":";
      pp ~ord:c.ideal.ord f ineq; Format.pp_print_string f " >= 0"; Format.pp_close_box f (); Format.pp_force_newline f ();
      Format.pp_open_box f 0; Format.pp_print_string f "Proof:"; Format.pp_open_vbox f 0; Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) (pp_used_th c) f uniq_ths; Format.pp_print_space f ();
      let pp_par fo id = 
        Format.pp_print_string fo "("; pp ~ord:c.ideal.ord fo (fst (BatIMap.find id c.ineqs)); Format.pp_print_string fo ")"
      in
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo " *"; Format.pp_print_space fo ()) pp_par f prods;
      Format.pp_print_string f " =";
      Format.pp_open_box f 0;
      Format.pp_print_space f ();
      pp_red c.ideal.ord f (eq_just.orig, get_generators c.ideal, eq_just.mults, ineq);
      Format.pp_close_box f ();
      Format.pp_close_box f ();
      Format.pp_force_newline f ();
      Format.pp_print_string f "QED";
      Format.pp_force_newline f ();
      Format.pp_close_box f ()
    | Given (eq_just, Some (head_eq_just, PosComb (pos_com, witness))) ->
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_force_newline fo ()) (pp_just c) f (List.map fst pos_com);
      Format.pp_open_hbox f (); Format.pp_print_string f "Theorem "; Format.pp_print_int f ineq_id; Format.pp_print_string f ":";
      pp ~ord:c.ideal.ord f ineq; Format.pp_print_string f " >= 0"; Format.pp_close_box f (); Format.pp_force_newline f ();
      Format.pp_open_box f 0; Format.pp_print_string f "Proof:"; Format.pp_open_vbox f 0; Format.pp_print_space f ();
      Format.pp_open_hbox f ();
      Format.pp_print_string f "Assumption: "; pp ~ord:c.ideal.ord f (head_eq_just.orig); Format.pp_print_string f " >=0  ==> "; pp ~ord:c.ideal.ord f (eq_just.orig);
      Format.pp_print_string f " >= 0";
      Format.pp_close_box f (); Format.pp_print_space f ();
      Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) (pp_used_th c) f (List.map fst pos_com); Format.pp_print_space f ();
      let eq_mults, eq_basis = head_eq_just.mults, get_generators c.ideal in
      let rem = from_const witness in
      let ineqs_used, ineq_mults = List.split (List.map (fun (id, coe) -> (fst (BatIMap.find id c.ineqs), from_const coe)) pos_com) in
      pp_red c.ideal.ord f (head_eq_just.orig, eq_basis @ ineqs_used, eq_mults @ ineq_mults, rem);
      Format.pp_print_space f ();
      pp_red c.ideal.ord f (eq_just.orig, eq_basis, eq_just.mults, ineq); 
      Format.pp_close_box f ();
      Format.pp_force_newline f ();
      Format.pp_print_string f "QED";
      Format.pp_force_newline f ();
      Format.pp_close_box f ()
    
  let pp_red f (eq_just, neg_comb, rem, c) = 
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_force_newline fo ()) (pp_just c) f (List.map snd neg_comb);
    Format.pp_open_hbox f (); Format.pp_print_string f "Theorem "; Format.pp_print_string f ":";
    pp ~ord:c.ideal.ord f eq_just.orig; Format.pp_print_string f " <= "; pp ~ord:c.ideal.ord f rem; Format.pp_close_box f (); Format.pp_force_newline f ();
    Format.pp_open_box f 0; Format.pp_print_string f "Proof:"; Format.pp_open_vbox f 0; Format.pp_print_space f ();
    Format.pp_open_vbox f 0;
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) (pp_used_th c) f (List.map snd neg_comb); Format.pp_print_space f ();
    Format.pp_close_box f ();
    let ineqs_used, ineq_mults = List.split (List.map (fun (coe, id) -> fst (BatIMap.find id c.ineqs), from_const coe) neg_comb) in 
    pp_red c.ideal.ord f (eq_just.orig, (get_generators c.ideal) @ ineqs_used, eq_just.mults @ ineq_mults, rem);
    Format.pp_force_newline f ();
    Format.pp_print_string f "QED";
    Format.pp_force_newline f ();
    Format.pp_close_box f ()

  let reduce_ineq ord p ineqs = 
    if is_const p then [], p
    else 
      let ids = BatISet.elements (BatIMap.domain ineqs) in
      if List.length ids = 0 then [], p
      else 
        let z3ctx = Z3.mk_context [] in
        let solver = Z3.Optimize.mk_opt z3ctx in
        let dim_map, p_dim, p_ineq = polys_to_dim ~ord:(Some ord) p ineqs in
        let lambdas = List.map (fun id -> (Z3.Arithmetic.Real.mk_const_s z3ctx ("lambda" ^ (string_of_int id)))) ids in
        Z3.Optimize.add solver (List.map (fun lambda -> Z3.Arithmetic.mk_le z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)) lambdas);
        let ineq_dim_lambda = List.combine lambdas ids in
      (*let add_pos_mult i ineq = 
        Lp.Poly.of_var (Lp.Var.make ~ub:0. ("lambda" ^ (string_of_int i))), ineq
      in
      let ineq_dim_lambda = List.mapi add_pos_mult ineq_dim in*)
        let generate_cnstrs dim _ (hard_cnsts, r_cnsts) = 
          let generate_lhs_sum sum (lambda, ineq_id) = 
            try 
              let dim_c = DimMap.find dim (BatIMap.find ineq_id p_ineq) in
              Z3.Arithmetic.mk_add z3ctx [sum; Z3.Arithmetic.mk_mul z3ctx [(Z3.Arithmetic.Real.mk_numeral_s z3ctx (Mon.to_string_c dim_c)); lambda]] 
            with Not_found -> sum
            in
          let sum = List.fold_left generate_lhs_sum (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) ineq_dim_lambda in
          let r = Z3.Arithmetic.Real.mk_const_s z3ctx ("r" ^ (string_of_int dim)) in
          let p_coef = 
            try Z3.Arithmetic.Real.mk_numeral_s z3ctx (Mon.to_string_c (DimMap.find dim p_dim))
            with Not_found -> Z3.Arithmetic.Real.mk_numeral_i z3ctx 0
          in
          let new_cnst = Z3.Boolean.mk_eq z3ctx (Z3.Arithmetic.mk_add z3ctx [sum; r]) p_coef in
          new_cnst :: hard_cnsts, r :: r_cnsts
        in
        let hard_cnsts, r_cnsts = DimMap.fold generate_cnstrs dim_map ([], []) in
        Z3.Optimize.add solver hard_cnsts;
        List.iteri (fun i r -> let _ = Z3.Optimize.add_soft solver (Z3.Boolean.mk_eq z3ctx r (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)) "1" (Z3.Symbol.mk_int z3ctx i) in ()) (List.rev r_cnsts);
        let _ = Z3.Optimize.maximize solver (Z3.Arithmetic.mk_add z3ctx lambdas) in
        match Z3.Optimize.check solver with
        | Z3.Solver.UNKNOWN | Z3.Solver.UNSATISFIABLE -> failwith "unable to solve linear program"
        | Z3.Solver.SATISFIABLE ->
          match Z3.Optimize.get_model solver with
          | None -> failwith "Z3 has no model"
          | Some model ->
            let collect_lambdas neg_comb (lambda, ineq_id) = 
              match (Z3.Model.get_const_interp_e model lambda) with
              | None -> failwith "Z3 model doesn't have a lambda"
              | Some lc ->
                let lambdac = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio lc) in
                if Mon.cmp lambdac (Mon.from_string_c "0") = 0 then neg_comb
                else
                  (lambdac, ineq_id) :: neg_comb
            in
            let neg_comb = List.fold_left collect_lambdas [] ineq_dim_lambda in
            let collect_remainder rem r_s = 
              match (Z3.Model.get_const_interp_e model r_s) with
              | None -> failwith "Z3 model doesn't have an r"
              | Some rv ->
                let rc = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio rv) in
                if Mon.cmp rc (Mon.from_string_c "0") = 0 then rem
                else
                  let r_string = Z3.Expr.to_string r_s in
                  let r_dim = int_of_string (String.sub r_string 1 ((String.length r_string) - 1)) in
                  (rc, DimMap.find r_dim dim_map) :: rem
            in
            let rem = from_mon_list (List.fold_left collect_remainder [] r_cnsts) in
            neg_comb, rem
        
  let reduce_eq p c = I.reduce p c.ideal

  let reduce p c = 
    let p_ired, mults = I.reduce_just p c.ideal in
    let neg_comb, p_ineq_red = reduce_ineq c.ideal.ord p_ired c.ineqs in
    let eq_just = {orig = p_ired; mults} in
    Log.log ~level:`debug pp_red (Some (eq_just, neg_comb, p_ineq_red, c));
    p_ineq_red
    

  let get_eq_basis c = I.get_generators c.ideal

  let get_ineq_basis c = 
    if List.length c.ineqs_prod = 0 then [I.from_const_s "0"]
    else
      let first_level = List.map List.hd (List.hd c.ineqs_prod) in
      List.map (fun i -> fst (BatIMap.find i c.ineqs)) first_level

  let saturate c impls = 
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
    aux c impls []

  let make_cone ?(sat = 1) ?(ord = I.grlex_ord) ?(eqs = []) ?(ineqs = []) ?(impls = []) () = 
    let ideal = make_ideal ord eqs in
    let red_add_ine co ine = 
      let ine_red, mults = I.reduce_just ine co.ideal in
      let eq_just = {orig = ine_red; mults} in
      add_ineq co ine_red (Given (eq_just, None))
    in
    let prod_sat_cone = List.fold_left red_add_ine {depth=sat; curr_num = 0; ideal= ideal; ineqs= BatIMap.empty ~eq:(fun _ _ -> false); ineqs_prod = []} ineqs in
    saturate prod_sat_cone impls

  let make_cone_i ?(sat = 1) ?(ineqs = []) ?(impls = []) ideal = 
    let red_add_ine co ine = 
      let ine_red, mults = I.reduce_just ine co.ideal in
      let eq_just = {orig = ine_red; mults} in
      add_ineq co ine_red (Given (eq_just, None))
    in
    let prod_sat_cone = List.fold_left red_add_ine {depth=sat; curr_num = 0; ideal= ideal; ineqs= BatIMap.empty ~eq:(fun _ _ -> false); ineqs_prod = []} ineqs in
    saturate prod_sat_cone impls
  
  let ppc f c = 
      Format.pp_print_string f "Cone:"; Format.pp_print_space f ();
      ppi f c.ideal;
      Format.pp_force_newline f ();
      if BatIMap.is_empty c.ineqs then Format.pp_print_string f "Ineqs: [0]"
      else
        Format.pp_open_hbox f ();
        Format.pp_print_string f "Basis Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp ~ord:c.ideal.ord) f (get_ineq_basis c);
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ();
        (*Format.pp_force_newline f ();
        Format.pp_open_hbox f ();
        Format.pp_print_string f "Derived Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp ~ord:c.ideal.ord) f (BatList.of_enum (BatEnum.map (fun (_, _, (i, _)) -> i) (BatIMap.enum c.ineqs)));
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ()*)

end

module ConeQ = Cone(Sigs.Q)

module IdealQ = Ideal(Sigs.Q)