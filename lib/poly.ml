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

  val is_const : poly -> coef option

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

  type impl = 
    | Buch
    | Fgb of (int BatMap.String.t) * (bool BatMap.String.t) * ((int * string) list)

  type ideal = {
    basis: generators;
    ord: Mon.monic_mon -> Mon.monic_mon -> int;
    impl:impl
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
    else if List.exists (fun (p, _) -> match is_const p with | Some _ -> true | None -> false) min_basis then
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
              match Mon.divide_mon (lt (List.nth g k)) lcmu with
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
        let lcmlt = Mon.lcm_of_mon (snd (lt fi)) (snd (lt fj)) in (* lt or lm? *)
        let prod = (Mon.mult_mon (lt fi) (lt fj)) in
        if criterion i j (Mon.from_string_c "1", lcmlt) then aux rest g
        else if Mon.lex_ord lcmlt (snd prod) = 0 then aux rest g (* criterion *)
        else (
          let sp = s_poly ord fi fj in
          let (_, (_, s)) = division ord g sp in
          match is_const (fst s) with
          | Some c ->
            if Mon.cmp c (Mon.from_string_c "0") = 0 then aux rest g
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
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ","; Format.pp_print_space fo ()) (pp ~ord:i.ord) f (List.map fst basis);
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
      {basis = Bot; ord; impl = Buch}
    else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal then 
      {basis = Top; ord; impl = Buch}
    else 
      improved_buchberger ord normal []
     

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
      {basis = Bot; ord; impl = Fgb (deg_map, keep_map, top_ord)}
    else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal then 
      {basis = Top; ord; impl = Fgb (deg_map, keep_map, top_ord)}
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
      if List.length normal_gb = 0 || List.for_all is_zero normal_gb then {basis = Bot; ord; impl = Fgb (deg_map, keep_map, top_ord)}
      else if List.exists (fun p -> match is_const p with | Some _ -> true | None -> false) normal_gb then {basis = Top; ord; impl = Fgb (deg_map, keep_map, top_ord)}
      else
        let sorted_gb = List.map (fun p -> make_sorted_poly ord (poly_sub p)) normal_gb in
        {basis = I sorted_gb; ord; impl = Fgb (deg_map, keep_map, top_ord)}

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

  let add_eqs i new_eqs =
    match i.impl with
    | Fgb (deg_map, keep_map, top_order) ->
      make_ideal_f deg_map keep_map top_order ((get_generators i) @ new_eqs)
    | Buch ->
      match i.basis with
      | Top -> {basis = Top; ord = i.ord; impl = Buch}
      | Bot -> improved_buchberger i.ord new_eqs []
      | I gs -> improved_buchberger i.ord new_eqs gs

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
  
  (*type posCom = PosComb of ((int * coef) list * I.coef)

  type derJust = eqJust * posCom*)

  type justification = 
   | Product of eqJust * (int list)
   | Given of eqJust (* * derJust option*)

  type cone = 
    {
      z3ctx : Z3.context;
      depth : int;
      ideal : I.ideal;
      curr_num : int;
      mutable curr_mon : int;
      mon_to_dim : (monic_mon, int) BatHashtbl.t;
      mutable dim_to_mon : (monic_mon BatIMap.t);
      ineqs : ((Mon.coef BatIMap.t) * justification) BatIMap.t;
      ineqs_prod : int list list list
    }

  let make_empty_cone depth ideal = 
    {z3ctx = Z3.mk_context []; depth; ideal; curr_num = 0; curr_mon = 0; mon_to_dim = BatHashtbl.create 50; dim_to_mon = BatIMap.empty ~eq:(fun a b -> Mon.lex_ord a b =0); ineqs = BatIMap.empty ~eq:(fun _ _ -> false); ineqs_prod = []}


  let get_dim c m = 
    try BatHashtbl.find c.mon_to_dim m
    with Not_found ->
      BatHashtbl.add c.mon_to_dim m c.curr_mon;
      c.dim_to_mon <- BatIMap.add c.curr_mon m c.dim_to_mon;
      c.curr_mon <- c.curr_mon + 1;
      c.curr_mon - 1

  let get_mon c dim = 
    try BatIMap.find dim c.dim_to_mon
    with Not_found -> failwith "Dim with no corresponding mon"

  let poly_to_dim c p =
    let mons = get_mons p in
    if BatEnum.is_empty mons then
      let (zero, zero_monic) = Mon.zero in
      BatIMap.singleton ~eq:(fun a b -> Mon.cmp a b = 0) (get_dim c zero_monic) zero
    else
      BatEnum.fold (fun map (coe, monic) -> BatIMap.add (get_dim c monic) coe map) (BatIMap.empty ~eq:(fun a b -> Mon.cmp a b = 0)) mons

  let dim_to_poly c dim_map = 
    from_mon_list (BatIMap.fold (fun dim coe l -> (coe, get_mon c dim) :: l) dim_map [])

  let get_eq_basis c = I.get_generators c.ideal

  let get_ineq_basis c = 
    if List.length c.ineqs_prod = 0 then [I.from_const_s "0"]
    else
      let first_level = List.map List.hd (List.hd c.ineqs_prod) in
      List.map (fun i -> (dim_to_poly c (fst (BatIMap.find i c.ineqs)))) first_level


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
    match I.is_const p with
    | Some c ->
      if I.Mon.cmp c (I.Mon.from_string_c "0") >= 0 then Some c
      else None
    | None -> None

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
      | (_, (Given _)) -> [id]
      | (_, (Product (_, l))) -> l
    ) lis in
    let ineqs_to_upgrade_prods = ineqs_to_prods ineqs_to_upgrade in
    let collect_ineqs_to_remove id (_, just) to_remove = 
      match just with
      | Product (_, prods) ->
        if List.exists (fun remove_pset -> is_factor remove_pset prods) ineqs_to_upgrade_prods then id :: to_remove
        else to_remove
      | _ -> to_remove
    in
    let ineqs_to_remove = BatIMap.fold collect_ineqs_to_remove c.ineqs ineqs_to_upgrade in
    let new_ineqs = List.fold_left (fun m i -> BatIMap.remove i m) c.ineqs ineqs_to_remove in
    let new_eqs = List.map (fun id -> dim_to_poly c (fst (BatIMap.find id c.ineqs))) ineqs_to_upgrade in
    let new_ideal = I.add_eqs c.ideal new_eqs in
    let folder id (_, just) (map, remove) = 
      let new_red, new_just = 
        match just with
        | Product (eq_just, prod_list) -> 
          let p_red, mults = I.reduce_just (eq_just.orig) new_ideal in
          p_red, Product({orig = eq_just.orig; mults}, prod_list)
        | Given (eq_just) -> 
          let p_red, mults = I.reduce_just (eq_just.orig) new_ideal in
          p_red, Given ({orig = eq_just.orig; mults})
      in
      match I.is_const new_red with
      | None -> BatIMap.add id (poly_to_dim c new_red, new_just) map, remove
      | Some c ->
        if Mon.cmp c (Mon.from_string_c "0") >= 0 then (map, id :: remove)
        else failwith "Created a contradiction"
    in
    let red_ineqs, is_to_remove = BatIMap.fold folder new_ineqs (BatIMap.empty ~eq:(fun _ _ -> false), ineqs_to_remove) in
    let is_to_remove_prod = ineqs_to_prods is_to_remove in
    let new_ineq_prod = List.map (fun pll -> List.filter (fun pl -> not (List.exists (fun r -> is_factor r pl) is_to_remove_prod)) pll) c.ineqs_prod in
    {c with ideal = new_ideal; ineqs = red_ineqs; ineqs_prod = new_ineq_prod}



  (* This function doesn't check whether incoming ine is already a member of the linear cone. Could consider an alternative*)
  let add_ineq c ine just : (cone * int list) = 
    let mult_and_minimize_ineqs (ineqs, curr_id) ins_to_add = 
      let reduce_and_just (inequs, id) prod = 
        let p = List.fold_left (fun acc ind -> I.mul acc (dim_to_poly c (fst (BatIMap.find ind inequs)))) (I.from_const_s "1") prod in
        let p_red, mults = I.reduce_just p c.ideal in
        match is_const_not_neg p_red with
        | Some _ -> inequs, id
        | None ->
          let eq_just = {orig = p; mults} in
          let new_ineqs = BatIMap.add id (poly_to_dim c p_red, Product (eq_just, prod)) inequs in
          new_ineqs, (id + 1)
      in
      List.fold_left reduce_and_just (ineqs, curr_id) ins_to_add
    in
    if not (is_const_not_neg ine = None) then c, []
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
      let ine_map = poly_to_dim c ine in
      let ineqs, next_id = mult_and_minimize_ineqs ((BatIMap.add poly_id (ine_map, just) (BatIMap.empty ~eq:(fun _ _ -> false))), poly_id + 1) prod_to_comput in
      {c with curr_num = next_id; ineqs; ineqs_prod = ineq_ladder}, List.init (next_id - poly_id) (fun i -> poly_id + i)
    else 
      let poly_id = c.curr_num in
      let folder (all_ineq, new_ineqs) curr_level = 
        if List.length all_ineq = 0 then [[poly_id] :: curr_level], new_ineqs
        else
          let prev_level = List.hd all_ineq in
          let new_ineq = List.map (fun p -> poly_id :: p) prev_level in
          (new_ineq @ curr_level) :: all_ineq, new_ineq @ new_ineqs
      in
      let ineqs_with_ine = BatIMap.add poly_id (poly_to_dim c ine, just) c.ineqs in
      let ineqs_ladder, ineqs_to_add = List.fold_left folder ([], []) c.ineqs_prod in
      let ineqs, next_id = mult_and_minimize_ineqs (ineqs_with_ine, poly_id + 1) ineqs_to_add in
      {c with curr_num = next_id; ineqs; ineqs_prod = List.rev ineqs_ladder}, List.init (next_id - poly_id) (fun i -> poly_id + i)


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

(*
  let get_z3_consts form = 
    let rec aux phi seen_asts consts = 
      if BatISet.mem (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts then seen_asts, consts
      else
        if Z3.Expr.is_const phi then 
          BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, BatISet.add ((Z3.Symbol.get_int % Z3.FuncDecl.get_name % Z3.Expr.get_func_decl) phi) consts
        else
          let children = Z3.Expr.get_args phi in
          if children = [] then BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) seen_asts, consts
          else
            let new_seen_asts, new_consts = List.fold_left (fun (pasts, pconsts) child -> aux child pasts pconsts) (seen_asts, consts) children in
            BatISet.add (Z3.AST.get_id (Z3.Expr.ast_of_expr phi)) new_seen_asts, new_consts
    in
    snd (aux form (BatISet.empty) (BatISet.empty))*)

(*
  let ppmodel c f model = 
    let model_interps = 
      List.fold_left (fun acc fun_decl -> 
        if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then acc (* Not a general solution *)
        else
          let interp = match Z3.Model.get_const_interp model fun_decl with
          | None -> failwith "Const has no interpretation in model"
          | Some e-> 
            Log.log_line_s ~level:`trace (Z3.Expr.to_string e);
            Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
          in
          (get_mon c (Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl)), interp) :: acc) [] (Z3.Model.get_const_decls model) in
    Format.pp_open_hvbox f 0;
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_space fo ()) (fun fo (monic, interp) -> ppmm fo monic; Format.pp_print_string fo (" = " ^ (Mon.to_string_c interp))) f model_interps
    *)
    

  let complete_and_evaluate_model m form (*c*) = 
    (*Log.log_line_s ~level:`trace "Trying to complete model: ";
    Log.log (ppmodel c) (Some m);*)
    (*let model_interps = 
      List.fold_left (fun map fun_decl -> 
        if Z3.Sort.get_sort_kind (Z3.FuncDecl.get_range fun_decl) = Z3enums.BOOL_SORT then map (* Not a general solution *)
        else
          let interp = match Z3.Model.get_const_interp m fun_decl with
          | None -> failwith "Const has no interpretation in model"
          | Some e-> 
            Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)
          in
          BatIMap.add (Z3.Symbol.get_int (Z3.FuncDecl.get_name fun_decl)) interp map) (BatIMap.empty ~eq:(fun a b -> Mon.cmp a b = 0)) (Z3.Model.get_const_decls m) in
    *)
    let partial_eval = match Z3.Model.eval m form true with | None -> failwith "Error evaluating model" | Some e -> e in
    partial_eval
    (*let rem_consts = get_z3_consts partial_eval in
    let folder dim (z3vare, z3interp) = 
      let mon = get_mon c dim in
      Log.log_s ~level:`trace "Trying to eval ";
      Log.log ~level:`trace ppmm (Some mon);
      let vars = Mon.get_vars mon in
      let var_interp = BatList.of_enum (BatEnum.map (fun v -> v, BatIMap.find (get_dim c (snd (Mon.make_mon_from_var v 1))) model_interps) vars) in
      let mon_interp = Mon.eval_monic var_interp mon in
      Log.log_s ~level:`trace ("Compound mon: " ^ (Mon.to_string_c mon_interp) ^ " = ");
      Log.log ~level:`trace ppmm (Some mon);
      Log.log_line_s ~level:`trace "Variable Assign";
      List.iter (fun (v, i) -> Log.log_line_s ~level:`trace (v ^ " = " ^ (Mon.to_string_c i))) var_interp;
      Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim) :: z3vare, Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c mon_interp) :: z3interp
    in
    let (vars, interps) = BatISet.fold folder rem_consts ([], []) in
    Z3.Expr.simplify (Z3.Expr.substitute partial_eval vars interps) None*)

  let saturate (c : cone) (impls : impl list) =
    let impls_red = 
      List.map 
        (fun (h, cons) -> 
          let (c_red, mults) = I.reduce_just cons c.ideal in
          (I.reduce h c.ideal, (c_red, {orig = cons; mults}))) impls
    in
    let const_dim = get_dim c (snd (Mon.make_mon_from_coef (Mon.from_string_c "0"))) in
    let dim_map_to_z3_ineq ineq = 
      let term_to_z3 dim coef = 
        if dim = const_dim then Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef)
        else
          Z3.Arithmetic.mk_mul c.z3ctx [Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef); Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim)]
      in
      Z3.Arithmetic.mk_ge c.z3ctx (Z3.Arithmetic.mk_add c.z3ctx (BatIMap.fold (fun d i l -> (term_to_z3 d i) :: l) ineq [])) (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)
    in
    let dim_map_to_z3_eq ineq = 
      let term_to_z3 dim coef = 
        if dim = const_dim then Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef)
        else
          Z3.Arithmetic.mk_mul c.z3ctx [Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef); Z3.Arithmetic.Real.mk_const c.z3ctx (Z3.Symbol.mk_int c.z3ctx dim)]
      in
      Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.mk_add c.z3ctx (BatIMap.fold (fun d i l -> (term_to_z3 d i) :: l) ineq [])) (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)
    in
    let solver = Z3.Solver.mk_simple_solver c.z3ctx in
    Z3.Solver.add solver (BatList.of_enum (BatEnum.map (fun (_, _, (i, _)) -> dim_map_to_z3_ineq i) (BatIMap.enum c.ineqs)));
    let z3_impls = List.map (fun (h, (cons, _)) -> dim_map_to_z3_ineq (poly_to_dim c h), dim_map_to_z3_ineq (poly_to_dim c cons)) impls_red in
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
            let (_, (ineq_to_add, just)) = List.nth impls_red id in
            let conee, added = add_ineq cone ineq_to_add (Given just) in
            let (added_id, non_lin) = match added with | [] -> failwith "Added no ineqs?" | x :: xs -> x, xs in
            let added_ineqs = (List.map (fun id -> dim_map_to_z3_ineq (fst (BatIMap.find id conee.ineqs))) non_lin) in
            Z3.Solver.add solver added_ineqs;
            let pot_eqs = (added_id, dim_map_to_z3_eq (fst (BatIMap.find added_id conee.ineqs)), false) :: List.map (fun id -> id, dim_map_to_z3_eq (fst (BatIMap.find id conee.ineqs)), false) non_lin in
            (conee, found_eqs, pot_eqs @ new_pot_eqs, added_ineqs @ new_ineqs))
          else
            (cone, id :: found_eqs, new_pot_eqs, new_ineqs)
        in
        let temp_cone, found_eqs, new_pot_eqs, new_ineqs = List.fold_left sort_cons_found_cons (co, [], [], []) found_cons in
        let cons_not_in_play_with_models = cons_not_in_play @ (List.map (fun (m, clist) -> m, (List.map (fun i -> List.nth cons_in_play i) clist)) violated_cons_and_models) in
        let new_ineqs_conj = Z3.Boolean.mk_and temp_cone.z3ctx new_ineqs in
        let (cons_not_in_play_this_round, new_pot_cons) = 
          List.partition (fun (m, _) -> 
            Z3.Boolean.is_true (complete_and_evaluate_model m new_ineqs_conj (*temp_cone*))) cons_not_in_play_with_models in
        Log.log_line_s ~level:`trace ("Found " ^ (string_of_int !num_found) ^ " new consequences");
        Log.log_line_s ~level:`trace ("Found " ^ (string_of_int (List.length found_eqs)) ^ " new equations");
        Log.log_line_s ~level:`trace ((string_of_int (List.length cons_not_in_play_this_round)) ^ " old cons are still violated in new form");
        find_all_cons (List.concat (new_pot_eqs :: List.map snd new_pot_cons)) cons_not_in_play_this_round (curr_num + List.length cons_in_play) (upgrade_ineqs temp_cone found_eqs)
    in
    find_all_cons (pot_eqs @ pot_ineqs) [] 0 c
  (*

  let upgrade_ineqs c ineqs_to_upgrade = 
    let collect_ineqs_to_remove id (_, just) to_remove = 
      match just with
      | Product (_, prod_list) ->
        if List.exists (fun pid -> List.mem pid ineqs_to_upgrade) prod_list then id :: to_remove
        else to_remove
      | _ -> to_remove
    in
    let ineqs_to_remove = BatIMap.fold collect_ineqs_to_remove c.ineqs ineqs_to_upgrade in
    let new_ineqs = List.fold_left (fun m i -> BatIMap.remove i m) c.ineqs ineqs_to_remove in
    let new_eqs = List.map (fun id -> fst (BatIMap.find id c.ineqs)) ineqs_to_upgrade in
    let new_ideal = I.add_eqs c.ideal new_eqs in
    let folder id (_, just) (map, remove) = 
      let new_red, new_just = 
        match just with
        | Product (eq_just, prod_list) -> 
          let p_red, mults = I.reduce_just (eq_just.orig) new_ideal in
          p_red, Product({orig = eq_just.orig; mults}, prod_list)
        | Given (eq_just, None) -> 
          let p_red, mults = I.reduce_just (eq_just.orig) new_ideal in
          p_red, Given ({orig = eq_just.orig; mults}, None)
        | Given (eq_just, Some (head_eq_just, PosComb (pos_comb, witness))) -> 
          let new_comb = List.filter (fun (id, _) -> not (List.mem id ineqs_to_remove)) pos_comb in
          let new_head_eq_just = {orig = head_eq_just.orig; mults = snd (I.reduce_just head_eq_just.orig new_ideal)} in
          let p_red, mults = I.reduce_just (eq_just.orig) new_ideal in
          p_red, Given ({orig = eq_just.orig; mults}, Some (new_head_eq_just, PosComb(new_comb, witness)))
      in
      match I.is_const new_red with
      | None -> BatIMap.add id (new_red, new_just) map, remove
      | Some c ->
        if Mon.cmp c (Mon.from_string_c "0") >= 0 then (map, id :: remove)
        else failwith "Created a contradiction"
    in
    let red_ineqs, is_to_remove = BatIMap.fold folder new_ineqs (BatIMap.empty ~eq:(fun _ _ -> false), ineqs_to_remove) in
    let new_ineq_prod = List.map (List.filter (List.for_all (fun id -> not (List.mem id is_to_remove)))) c.ineqs_prod in
    {depth = c.depth; curr_num = c.curr_num; ideal = new_ideal; ineqs = red_ineqs; ineqs_prod = new_ineq_prod}





  let normalize c = 
    let rec check_line co =
      let dim_map, _, p_ineq = polys_to_dim ~ord:None (I.from_const_s "0") co.ineqs in
      let ids = BatISet.elements (BatIMap.domain p_ineq) in
      let z3ctx = Z3.mk_context [] in
      let solver = Z3.Solver.mk_simple_solver z3ctx in
      let lambdas = List.map (fun id -> (Z3.Arithmetic.Real.mk_const_s z3ctx ("lambda" ^ (string_of_int id)))) ids in
      Z3.Solver.add solver (List.map (fun lambda -> Z3.Arithmetic.mk_ge z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)) lambdas); (*lambda >= 0*)
      if lambdas = [] then 
        Z3.Solver.add solver [(Z3.Arithmetic.mk_gt z3ctx (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0))] (* 0 > 0*)
      else
        Z3.Solver.add solver [(Z3.Arithmetic.mk_gt z3ctx (Z3.Arithmetic.mk_add z3ctx lambdas) (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0))]; (* sum lambda > 0*)
      let ineq_dim_lambda = List.combine lambdas ids in
      let generate_cnstrs dim m r_var = 
        let generate_lhs_sum sum (lambda, ineq_id) = 
          try 
            let dim_c = DimMap.find dim (BatIMap.find ineq_id p_ineq) in
            Z3.Arithmetic.mk_add z3ctx [sum; Z3.Arithmetic.mk_mul z3ctx [(Z3.Arithmetic.Real.mk_numeral_s z3ctx (Mon.to_string_c dim_c)); lambda]] 
          with Not_found -> sum
        in
        let sum = List.fold_left generate_lhs_sum (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) ineq_dim_lambda in
        if I.Mon.is_const (I.Mon.from_string_c "0", m) then
          let r = Z3.Arithmetic.Real.mk_const_s z3ctx "r" in
          Z3.Solver.add solver [Z3.Arithmetic.mk_le z3ctx r (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0)]; (* r <= 0*)
          Z3.Solver.add solver [Z3.Boolean.mk_eq z3ctx r (Z3.Arithmetic.mk_add z3ctx [sum; r])];   (* r = sum (lambda_i q_i) for i const dim*)
          Some r
        else
          (Z3.Solver.add solver [Z3.Boolean.mk_eq z3ctx (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) sum]; (* 0 = sum (lambda_i q_i) for i non-const dim*)
          r_var)
      in
      let r_opt = DimMap.fold generate_cnstrs dim_map None in
      let r = 
        match r_opt with 
        | Some v -> v 
        | None -> 
          let re = Z3.Arithmetic.Real.mk_const_s z3ctx "r" in
          Z3.Solver.add solver [Z3.Boolean.mk_eq z3ctx (Z3.Arithmetic.Real.mk_numeral_i z3ctx 0) re];
          re  
      in
      match (*Log.log_time_cum "z3 solve upgrade"*) (Z3.Solver.check solver) [] with
      | Z3.Solver.UNKNOWN | Z3.Solver.UNSATISFIABLE -> co
      | Z3.Solver.SATISFIABLE ->
        Log.log_line_s ~level:`trace "found implied eq";
        match Z3.Solver.get_model solver with
        | None -> failwith "check is sat but no model?"
        | Some model ->
          (match Z3.Model.get_const_interp_e model r with
          | None -> failwith "model doesn't have interpretation for r"
          | Some rv ->
            if Mon.cmp (Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio rv)) (Mon.from_string_c "0") = 0 then ()
            else failwith "Contradiction in inequalities");
          let collect_new_eqs new_eqs (lambda, ineq_id) = 
            match Z3.Model.get_const_interp_e model lambda with
            | None -> failwith "model doesn't have interpretation for a lambda"
            | Some v ->
              let lambdac = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio v) in
              if Mon.cmp lambdac (Mon.from_string_c "0") = 0 then new_eqs
              else
                ineq_id :: new_eqs
          in
          let new_eqs = List.fold_left collect_new_eqs [] ineq_dim_lambda in
          check_line (upgrade_ineqs co new_eqs)
    in
    check_line c  *)


  (*let pp_used_th c fo id = 
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
    *)

  let preprocess_ineqs p c = 
    let (_, lm) = I.lt (I.make_sorted_poly c.ideal.ord p) in
    let const_dim = BatISet.choose (BatIMap.domain (poly_to_dim c (from_const_s "0"))) in
    let folder id (ineq, _) (consts, parity_map) = 
      let ineq_list = List.sort (fun i j -> (-1) * (c.ideal.ord (BatIMap.find i c.dim_to_mon) (BatIMap.find j c.dim_to_mon))) (BatISet.elements (BatIMap.domain ineq)) in
      if List.length ineq_list = 0 then (id :: consts, parity_map)
      else if List.length ineq_list = 1 && const_dim = List.hd ineq_list then 
        let dim_coef = BatIMap.find (List.hd ineq_list) ineq in
        if Mon.cmp dim_coef (Mon.from_string_c "0") < 0 then failwith "Negative const in polyhedron"
        else (id :: consts, parity_map)
      else
        let bigger_mons = List.filter (fun i -> c.ideal.ord (BatIMap.find i c.dim_to_mon) lm > 0) ineq_list in
        let update_map map dim = 
          if BatIMap.mem dim map then
            (match BatIMap.find dim map with
            | None -> map
            | Some par -> 
              let dim_coef = BatIMap.find dim ineq in
              if Mon.cmp dim_coef (Mon.from_string_c "0") = 0 then failwith "ineq has 0 coeficient";
              let dim_par = if Mon.cmp dim_coef (Mon.from_string_c "0") > 0 then 1 else (-1) in
              if par = dim_par then map
              else BatIMap.modify dim (fun _ -> None) map)
          else
            let dim_coef = BatIMap.find dim ineq in
            if Mon.cmp dim_coef (Mon.from_string_c "0") = 0 then failwith "ineq has 0 coeficient";
            let dim_par = if Mon.cmp dim_coef (Mon.from_string_c "0") > 0 then 1 else (-1) in
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
                | None -> Some (Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef))])
                | Some e -> Some (Z3.Arithmetic.mk_add c.z3ctx [e; Z3.Arithmetic.mk_mul c.z3ctx [lambda; (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c coef))]])
              ) map
          in
          Z3.Optimize.add solver [Z3.Arithmetic.mk_le c.z3ctx lambda (Z3.Arithmetic.Real.mk_numeral_i c.z3ctx 0)];
          BatIMap.fold collect_ineq_dims ineq dim_sum_map, lambda :: ls
        in
        let dim_sum_map, lambdas = BatIMap.fold folder preprocessed_ineqs (BatIMap.empty ~eq:(fun _ _ -> false), []) in
        Log.log_line_s ~level:`trace (string_of_int (BatISet.cardinal (BatIMap.domain dim_sum_map)) ^ " dimensions");
        Log.log_line_s ~level:`trace ((string_of_int (List.length lambdas)) ^ " ineqs");
        let p_dim_map = poly_to_dim c p in
        let dims_sorted_small_to_big = 
          List.sort (fun i_dim j_dim -> c.ideal.ord (BatIMap.find i_dim c.dim_to_mon) (BatIMap.find j_dim c.dim_to_mon)) 
            (BatISet.elements (BatISet.union (BatIMap.domain dim_sum_map) (BatIMap.domain p_dim_map))) in
        let dims_and_r_cons = List.map
          (fun dim -> 
            let r = Z3.Arithmetic.Real.mk_const_s c.z3ctx ("r" ^ (string_of_int dim)) in
            if BatIMap.mem dim p_dim_map && BatIMap.mem dim dim_sum_map then
              (let p_coef = BatIMap.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c p_coef)) (Z3.Arithmetic.mk_add c.z3ctx [r; BatIMap.find dim dim_sum_map])]; (* p_c = sum lambda_i + r *)
              (dim, r))
            else if BatIMap.mem dim p_dim_map then
              (let p_coef = BatIMap.find dim p_dim_map in
              Z3.Optimize.add solver [Z3.Boolean.mk_eq c.z3ctx (Z3.Arithmetic.Real.mk_numeral_s c.z3ctx (Mon.to_string_c p_coef)) r]; (* p_c = r*)
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
                let rc = Mon.of_zarith_q (Z3.Arithmetic.Real.get_ratio rv) in
                if Mon.cmp rc (Mon.from_string_c "0") = 0 then rem
                else
                  (rc, BatIMap.find r_dim c.dim_to_mon) :: rem
            in
            let rem = from_mon_list (List.fold_left collect_remainder [] dims_and_r_cons) in
            [], rem
        
  let reduce_eq p c = I.reduce p c.ideal

  let reduce p c = 
    let p_ired, (*mults*)_ = Log.log_time_cum "reduce eq" (I.reduce_just p) c.ideal in
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

  
  let make_cone ?(sat = 1) ?(ord = I.grlex_ord) ?(eqs = []) ?(ineqs = []) ?(impls = []) () = 
    let ideal = make_ideal ord eqs in
    let red_add_ine co ine = 
      let ine_red, mults = I.reduce_just ine co.ideal in
      let eq_just = {orig = ine_red; mults} in
      fst (add_ineq co ine_red (Given (eq_just)))
    in
    let prod_sat_cone = List.fold_left red_add_ine (make_empty_cone sat ideal) ineqs in
    let unnormal_c = saturate prod_sat_cone impls in
    (*normalize unnormal_c*)
    unnormal_c

  let make_cone_i ?(sat = 1) ?(ineqs = []) ?(impls = []) ideal = 
    let red_add_ine co ine = 
      let ine_red, mults = I.reduce_just ine co.ideal in
      let eq_just = {orig = ine_red; mults} in
      fst (add_ineq co ine_red (Given (eq_just)))
    in
    let prod_sat_cone = 
      Log.log_time_cum "prod sat" (List.fold_left red_add_ine (make_empty_cone sat ideal)) ineqs in
    let unnormal_c = Log.log_time_cum "impl sat" (saturate prod_sat_cone) impls in
    (*Log.log_time_cum "normalize" normalize unnormal_c*)
    unnormal_c
  

end

module ConeQ = Cone(Sigs.Q)

module IdealQ = Ideal(Sigs.Q)