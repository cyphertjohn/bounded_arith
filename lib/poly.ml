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
    let filtered_list = List.filter_map (fun (m, (b, _)) -> if is_zero m then None else Some (m, b)) (List.combine mults basis) in
    if List.length filtered_list = 0 then ()
    else 
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
      let (reduction_occurred, (mults, rem)) = division i.ord basis (make_sorted_poly i.ord p) in
      if not reduction_occurred then Log.log ~level:`trace (pp_red i.ord) None
      else Log.log ~level:`trace (pp_red i.ord) (Some (p, basis, mults, fst rem));
      fst rem


  let make_ideal ord eqs : ideal = 
    let normal = List.filter (fun p -> not (is_zero p)) eqs in
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
      if grevlex_bk1 <> 0 then grevlex_bk1
      else
        let m1d_bk_2 = List.map (fun v -> effective_deg v * Mon.degree v m1) bk2 in
        let m2d_bk_2 = List.map (fun v -> effective_deg v * Mon.degree v m2) bk2 in
        let m1bk2tot, m2bk2tot = List.fold_left (+) 0 m1d_bk_2, List.fold_left (+) 0 m2d_bk_2 in
        if m1bk2tot = m2bk2tot then
          try (List.find ((<>) 0) (List.rev (List.map2 (-) m1d_bk_2 m2d_bk_2)))
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

  (*let sub_faugere_ideal_to_ideal ord i svar_to_pvar = 
    match i.basis with
    | Top -> {basis = Top; ord}
    | Bot -> {basis = Bot; ord}
    | I ps ->
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
      let sub_polys = List.map (fun p -> make_sorted_poly ord (poly_sub (fst p))) ps in
      {basis = I sub_polys; ord}*)
     

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

    type ideal

    type poly

    type monic_mon

    type impl = poly * poly

    val (=>) : poly -> poly -> impl

    val make_cone : ?sat:int -> ?ord:(monic_mon -> monic_mon -> int) -> ?eqs:poly list -> ?ineqs:poly list -> ?impls: impl list -> unit -> cone

    val make_cone_i : ?sat:int -> ?ineqs:poly list -> ?impls:impl list -> ideal -> cone

    val is_non_neg : poly -> cone -> bool

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

  type cone = 
    {
      depth : int;
      ideal : I.ideal;
      curr_num : int;
      first_level : poly BatIMap.t;
      ineqs : (poly * int list) list list
    }

  (*type cone = int * I.ideal * poly list list*)

  let is_not_neg_const p = 
    if I.is_const p then
      let c = fst (List.hd (BatList.of_enum (I.get_mons p))) in
      if I.Mon.cmp c (I.Mon.from_string_c "0") >= 0 then true
      else false
    else false

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
  let add_ineq c ine : cone = 
    let minimize_ineqs ins = 
      let reduced_ineqs = List.map (fun i -> I.reduce (fst i) c.ideal, snd i) ins in
      List.filter (fun p -> not (is_not_neg_const (fst p))) reduced_ineqs
    in
    let ine_red = I.reduce ine c.ideal in
    if is_not_neg_const ine_red then c
    else if BatIMap.is_empty c.first_level then 
      let poly_id = c.curr_num in
      let rec dup v t = if t <=0 then [] else v :: (dup v (t-1)) in
      let rec aux acc depth = 
        if depth <= 0 then acc
        else 
          aux ([I.exp_poly ine_red depth, dup poly_id depth] :: acc) (depth - 1)
      in
      {depth = c.depth; ideal = c.ideal; curr_num = (poly_id + 1); first_level = BatIMap.add poly_id ine_red c.first_level; ineqs= (List.map minimize_ineqs (aux [] c.depth))}
    else 
      let poly_id = c.curr_num in
      let folder acc curr_level = 
        if List.length acc = 0 then [(ine_red, [poly_id]) :: curr_level]
        else
          let prev_level = List.hd acc in
          ((List.map (fun p -> I.mul ine_red (fst p), poly_id :: (snd p)) prev_level) @ curr_level) :: acc
      in
      let new_ineqs = List.map minimize_ineqs (List.rev (List.fold_left folder [] c.ineqs)) in
      {depth = c.depth; ideal = c.ideal; curr_num = (poly_id + 1); first_level = BatIMap.add poly_id ine_red c.first_level; ineqs= new_ineqs}


  module MonMap = BatHashtbl

  module DimMap = BatIMap

  module S = BatMap.Make(struct type t = Lp.Poly.t let compare = Lp.Poly.compare end)

  let polys_to_dim ?ord:(ord = None) polys = 
    let mon_map = MonMap.create (10 * (List.length polys)) in
    let add_mons poly = 
      BatEnum.iter (fun (_, m) -> MonMap.modify_def 0 m (fun _ -> 0) mon_map) (get_mons poly)
    in
    List.iter add_mons polys;
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
    let poly_to_coef_map poly = 
      BatEnum.fold (fun acc (c, mon) -> 
        let dim = MonMap.find mon_map mon in
        DimMap.add dim c acc) (DimMap.empty ~eq:(fun x y -> Mon.cmp x y = 0)) (get_mons poly)
    in
    dim_map, List.map poly_to_coef_map polys
    
  (*let pp_prob f prob = 
    let prob_str = Lp.Problem.to_string ~short:true prob in
    Format.pp_print_string f prob_str;
    Format.print_newline ()*)


  let is_non_neg p c = 
    let id, ineqs = c.ideal, c.ineqs in
    let p_ired = I.reduce p id in
    if is_not_neg_const p_ired then true
    else if I.is_const p_ired then false
    else
      let ineqs = List.concat (List.map (List.map fst) ineqs) in
      let dim_map, p_ineq = polys_to_dim ~ord:None (p_ired :: ineqs) in
      let p_dim = List.hd p_ineq in
      let ineq_dim = List.tl p_ineq in
      let lambdas = Array.to_list (Lp.Poly.range ~lb:0. ~start:0 (List.length ineq_dim) "lambda") in
      let ineq_dim_lambda = List.map2 (fun lambda ineq -> lambda, ineq) lambdas ineq_dim in
      let generate_cnstrs dim m cnsts = 
        let generate_lhs_sum sum (lambda, ineq) = 
          try 
            let dim_c = DimMap.find dim ineq in
            Lp.Poly.(++) sum (Lp.Poly.expand (Lp.Poly.c (Mon.to_float dim_c)) lambda)
          with Not_found -> sum
          in
        let sum = List.fold_left generate_lhs_sum (Lp.Poly.zero) ineq_dim_lambda in
        let p_coef = 
          try Lp.Poly.c (Mon.to_float (DimMap.find dim p_dim))
          with Not_found -> Lp.Poly.zero
        in
        if I.Mon.is_const (I.Mon.from_string_c "0", m) then
          let r = Lp.Poly.var ~lb:0. "r" in
          let new_cnst = Lp.Cnstr.eq (Lp.Poly.(++) sum r) p_coef in
          new_cnst :: cnsts
        else
          let new_cnst = Lp.Cnstr.eq sum p_coef in
          new_cnst :: cnsts
      in
    let cnstrs = DimMap.fold generate_cnstrs dim_map [] in
    let prob = Lp.Problem.make (Lp.Objective.minimize Lp.Poly.zero) cnstrs in
    match Lp_glpk.solve ~term_output:false prob with
    | Ok _ -> true
    | Error _ -> false

  let pp_red f (t, lambda_ps, rem) = 
    Format.pp_open_box f 0; pp f t; Format.pp_print_string f " ="; 
    Format.pp_open_hvbox f 0;
    pp f rem; Format.pp_print_string f " +"; Format.pp_print_space f ();
    let pp_lambdas fo (lambda, b) = 
      Format.pp_open_box fo 0; 
      Format.pp_print_string fo (Mon.to_string_c lambda);
      Format.pp_print_string fo "("; pp fo b; Format.pp_print_string fo ")";
      Format.pp_close_box fo ()
    in
    Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo " +"; Format.pp_print_space fo ()) pp_lambdas f lambda_ps;
    Format.pp_close_box f (); Format.pp_close_box f ()

  let reduce_ineq ord p ineqs = 
    if is_const p then p
    else if List.length ineqs = 0 then p
    else 
      let dim_map, p_ineq = polys_to_dim ~ord:(Some ord) (p :: ineqs) in
      let p_dim = List.hd p_ineq in
      let ineq_dim = List.tl p_ineq in
      let lambdas = Array.to_list (Lp.Poly.range ~lb:Float.neg_infinity ~ub:0. ~start:0 (List.length ineq_dim) "lambda") in
      let ineq_dim_lambda = List.map2 (fun lambda ineq -> lambda, ineq) lambdas ineq_dim in
      (*let add_pos_mult i ineq = 
        Lp.Poly.of_var (Lp.Var.make ~ub:0. ("lambda" ^ (string_of_int i))), ineq
      in
      let ineq_dim_lambda = List.mapi add_pos_mult ineq_dim in*)
      let generate_cnstrs dim _ (hard_cnsts, r_cnsts, r_map) = 
        let generate_lhs_sum sum (lambda, ineq) = 
          try 
            let dim_c = DimMap.find dim ineq in
            Lp.Poly.(++) sum (Lp.Poly.expand (Lp.Poly.c (Mon.to_float dim_c)) lambda)
          with Not_found -> sum
          in
        let sum = List.fold_left generate_lhs_sum (Lp.Poly.zero) ineq_dim_lambda in
        let r = Lp.Poly.var ~lb:Float.neg_infinity ("r" ^ (string_of_int dim)) in
        let p_coef = 
          try Lp.Poly.c (Mon.to_float (DimMap.find dim p_dim))
          with Not_found -> Lp.Poly.zero
        in
        let new_cnst = Lp.Cnstr.eq (Lp.Poly.(++) sum r) p_coef in
        let r_zero = Lp.Cnstr.eq r Lp.Poly.zero in
        new_cnst :: hard_cnsts, r_zero :: r_cnsts, S.add r dim r_map
      in
      let hard_cnsts, r_cnsts, r_to_dim = DimMap.fold generate_cnstrs dim_map ([], [], S.empty) in
      let rec find_optimal_sol rs = 
        let prob = Lp.Problem.make (Lp.Objective.minimize (BatEnum.fold Lp.Poly.(++) (Lp.Poly.zero) (S.keys r_to_dim))) (hard_cnsts @ rs) in
        (*Log.log ~level:`trace pp_prob prob;*)
        match Lp_glpk.solve ~term_output:false prob with
        | Ok (_, s) ->
          let collect_lambdas neg_comb (lambda, ineq_dim) = 
            let lambdac = Mon.of_float (Lp.PMap.find lambda s) in
            if Mon.cmp lambdac (Mon.from_string_c "0") = 0 then neg_comb
            else
              let ineq = DimMap.fold (fun dim coef acc -> (coef, DimMap.find dim dim_map) :: acc) ineq_dim [] in 
              (lambdac, from_mon_list ineq) :: neg_comb
          in
          let neg_comb = List.fold_left collect_lambdas [] ineq_dim_lambda in
          let collect_remainder r_s r_dim rem = 
            let rc = Mon.of_float (Lp.PMap.find r_s s) in
            if Mon.cmp rc (Mon.from_string_c "0") = 0 then rem
            else
              (rc, DimMap.find r_dim dim_map) :: rem
          in
          let rem = from_mon_list (S.fold collect_remainder r_to_dim []) in
          neg_comb, rem
        | Error _ -> find_optimal_sol (List.tl rs)
      in
      let neg_comb, rem = find_optimal_sol r_cnsts in
      Log.log ~level:`trace pp_red (Some (p, neg_comb, rem));
      rem
        
  let reduce_eq p c = I.reduce p c.ideal

  let reduce p c = 
    let p_ired = I.reduce p c.ideal in
    let p_ineq_red = reduce_ineq c.ideal.ord p_ired (List.concat (List.map (List.map fst) c.ineqs)) in
    p_ineq_red
    

  let get_eq_basis c = I.get_generators c.ideal

  let get_ineq_basis c = 
    if List.length c.ineqs = 0 then [I.from_const_s "0"]
    else
      List.map fst (List.hd c.ineqs)

  let saturate c impls = 
    let rec aux curr_cone worklist tried = 
      match worklist with
      | [] -> curr_cone
      | (imp, con) :: rest ->
        if is_non_neg imp curr_cone then aux (add_ineq curr_cone con) (rest @ tried) []
        else
          aux curr_cone rest ((imp, con) :: tried)
    in
    aux c impls []

  let make_cone ?(sat = 1) ?(ord = I.grlex_ord) ?(eqs = []) ?(ineqs = []) ?(impls = []) () = 
    let ideal = make_ideal ord eqs in
    let prod_sat_cone = List.fold_left add_ineq {depth=sat; curr_num = 0; first_level = BatIMap.empty ~eq:I.equal; ideal= ideal; ineqs= []} ineqs in
    saturate prod_sat_cone impls

  let make_cone_i ?(sat = 1) ?(ineqs = []) ?(impls = []) ideal = 
    let prod_sat_cone = List.fold_left add_ineq {depth=sat; curr_num = 0; first_level = BatIMap.empty ~eq:I.equal; ideal= ideal; ineqs= []} ineqs in
    saturate prod_sat_cone impls

  let ppc f c = 
      Format.pp_print_string f "Cone:"; Format.pp_print_space f ();
      ppi f c.ideal;
      Format.pp_force_newline f ();
      if List.length c.ineqs = 0 then Format.pp_print_string f "Ineqs: [0]"
      else
        Format.pp_open_hbox f ();
        Format.pp_print_string f "Basis Ineqs:";
        Format.print_space ();
        Format.pp_print_string f "["; 
        Format.pp_open_box f 0;
        Format.pp_print_list ~pp_sep: (fun fo () -> Format.pp_print_string fo ";"; Format.pp_print_space fo ()) (pp ~ord:c.ideal.ord) f (List.map fst (List.hd c.ineqs));
        Format.pp_print_string f "]";
        Format.pp_close_box f (); Format.pp_close_box f ()

end

module ConeQ = Cone(Sigs.Q)

module IdealQ = Ideal(Sigs.Q)