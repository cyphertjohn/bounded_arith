
module MakeMon (C : Sigs.Coefficient) (V : Sigs.Var) = struct

  type var = V.t

  type varset = V.S.set

  type pre_monic = (V.t * int) list

  let pre_monic_to_deg_map : pre_monic -> V.Mi.map = List.fold_left (fun degmap (v, d) -> V.Mi.add v d degmap) (V.Mi.empty)

  let mon_to_dim = BatHashtbl.create 100
  let dim_to_mon = BatHashtbl.create 100

  let curr_mon = ref 0

  let get_dim (m : pre_monic) = 
    try BatHashtbl.find mon_to_dim m
    with Not_found ->
      BatHashtbl.add mon_to_dim m !curr_mon;
      BatHashtbl.add dim_to_mon !curr_mon (m, pre_monic_to_deg_map m);
      curr_mon := !curr_mon + 1;
      !curr_mon - 1

  let get_mon dim : pre_monic = 
    try fst (BatHashtbl.find dim_to_mon dim)
    with Not_found -> failwith "Dim with no corresponding mon"

  type monic_mon = int

  type mon = C.coef * monic_mon

  let mon_to_id (m : monic_mon) : int = m

  let id_to_mon (m : int) : monic_mon = m

  let zero_mon = get_dim []

  let make_mon_from_coef (c : C.coef) : mon = (c, zero_mon)

  let make_mon_from_var s i : mon = (C.from_string_c "1", get_dim [(s, i)])

  let mon_from_coef c = (C.from_string_c c, zero_mon)

  let make_mon_from_faugere_mon vars (c, elist) : mon = 
    let folder acc v e = 
      if e > 0 then 
        (v, e) :: acc
      else acc
    in
    let monic = List.fold_left2 folder [] vars elist in
    let monic = List.sort (fun (av, _) (bv, _)-> V.compare av bv) monic in
    C.of_zarith c, (get_dim monic)

  let zero = make_mon_from_coef (C.zero)

  let minus_1 = mon_from_coef "-1"

  let is_zero ((c, m) : mon) = 
    if C.is_zero c then
      if m = zero_mon then true
      else failwith "Monomial has zero coefficient but is not empty"
    else false

  let is_one ((c, m) : mon) =
    if C.is_one c && m = zero_mon then true
    else false
  
  (*let get_monic_mon (N (_, mon)) = mon
  
  let get_coef (N (Coef c, _)) = c*)

  (*let add_mon (a : mon) (b : mon) = 
    if is_zero a then Some b
    else if is_zero b then Some a
    else
      let (ac, amon), (bc, bmon) = (a, b) in
      if BatMap.String.equal (=) amon bmon then 
        let c = C.addc ac bc in
        if C.is_zero c then Some zero
        else Some (c, amon)
      else None*)
    

  let mult_mon ((ac, am) : mon) ((bc, bm) : mon) : mon = 
    let new_coef = C.mulc ac bc in
    if (C.is_zero new_coef) then zero
    else 
      let rec zip acc am bm = 
        match am, bm with
        | [], [] -> List.rev acc
        | _ :: _ , [] -> (List.rev acc) @ am
        | [], _ :: _ -> (List.rev acc) @ bm
        | (av, ae) :: a_rest, (bv, be) :: b_rest ->
          if V.equal av bv then
            zip ((av, ae + be) :: acc) a_rest b_rest
          else if V.compare av bv < 0 then
            zip ((av, ae) :: acc) a_rest bm
          else
            zip ((bv, be) :: acc) am b_rest
        in
      (new_coef, (get_dim (zip [] (get_mon am) (get_mon bm))))
  
  let divide_mon ((ac, am) : mon) ((bc, bm) : mon) : mon option = 
    if C.is_zero bc then failwith "Divide by 0";
    let new_coef = C.divc ac bc in
    let rec var_divide rema remb (acc) =
      match (rema, remb) with
      | [], [] -> Some (List.rev acc)
      | [], _ :: _ -> None
      | _, [] -> Some ((List.rev acc) @ rema)
      | (av, ae) :: remas, (bv, be) :: rembs ->
        if V.equal av bv && ae = be then var_divide remas rembs (acc)
        else if V.equal av bv && ae > be then var_divide remas rembs (((av, ae - be)) :: acc)
        else if V.equal av bv && ae < be then None
        else if V.compare av bv < 0 then var_divide remas remb (((av, ae)) :: acc)
        else None
    in
    match (var_divide (get_mon am) (get_mon bm) []) with
    | None -> None
    | Some new_mon -> Some (new_coef, get_dim new_mon)
  
  let lcm_of_mon (a : monic_mon) (b : monic_mon) : monic_mon = 
    let rec aux x y acc =
      match (x, y) with
      | ([], _) -> y @ acc
      | (_, []) -> x @ acc
      | ((xvar, e1) :: xs, (yvar, e2) :: ys) -> 
        if V.equal xvar yvar then (xvar, max e1 e2) :: (aux xs ys acc)
        else if V.compare xvar yvar < 0 then (xvar, e1) :: (aux xs y acc)
        else (yvar, e2) :: (aux ys x acc)
    in
    get_dim (aux (get_mon a) (get_mon b) [])

  let degree v (m : monic_mon) : int = 
    try V.Mi.find v (snd (BatHashtbl.find dim_to_mon m))
    with Not_found -> 0

  let get_vars (m : monic_mon) = 
    V.Mi.domain (snd (BatHashtbl.find dim_to_mon m))

  let monic_mon_to_string (m : monic_mon) = 
    let folder acc (v, e) = 
      if e > 1 then ((V.to_string v) ^ "^" ^ (string_of_int e)) :: acc
      else (V.to_string v) :: acc
    in
    String.concat "" (List.rev (List.fold_left folder [] (get_mon m)))

  let is_const ((_, m) : mon) = m = zero_mon

  let mon_to_string ((c, m) : mon) =
    let is_neg, norm_c = 
      if C.cmp c C.zero < 0 then true, (C.mulc c (C.from_string_c "-1"))
      else false, c
    in
    if is_const (c, m) then is_neg, C.to_string_c norm_c
    else if C.is_one norm_c then is_neg, (monic_mon_to_string m)
    else is_neg, (C.to_string_c norm_c) ^ (monic_mon_to_string m)

  let lex_ord (m1 : monic_mon) (m2 : monic_mon) : int = 
    let rec aux a b = 
      match (a, b) with
      | ([], []) -> 0
      | ([], _ :: _) -> -1
      | (_ :: _, []) -> 1
      | ((xv, xe) :: xs, (yv, ye) :: ys) -> 
        if V.equal xv yv then 
          if compare xe ye = 0 then aux xs ys
          else compare xe ye
        else if V.compare xv yv < 0 then 1
        else (-1)
    in
    aux (get_mon m1) (get_mon m2)

  let total_deg (m : monic_mon) = 
    List.fold_left (fun acc (_, e) -> e + acc) 0 (get_mon m)


  let grlex_ord (a : monic_mon) (b : monic_mon) = 
    let a_deg = total_deg a in
    let b_deg = total_deg b in
    if compare a_deg b_deg = 0 then lex_ord a b
    else compare a_deg b_deg

  let ord = ref lex_ord

  let mon_ord ((c1, m1) : mon) ((c2, m2) : mon) = 
    let order = !ord m1 m2 in
    if order = 0 then C.cmp c1 c2 else order

  let eval_monic eval_list (mon : monic_mon) = 
    if mon = zero_mon  then C.zero
    else
      let eval_list_s = List.sort (fun (av, _) (bv, _) -> V.compare av bv) eval_list in
      let rec aux res elist monlist = 
        match elist, monlist with
        | [], [] -> res
        | _, [] -> res
        | [], (v, _) :: _ -> failwith ("No evaluation for " ^ (V.to_string v))
        | (evar, eval) :: erest, (mv, me) :: mrest ->
          if compare evar mv < 0 then aux res erest monlist
          else if compare evar mv > 0 then failwith ("No evaluation for " ^ (V.to_string mv))
          else aux (C.mulc res (C.exp eval me)) erest mrest
      in
      aux C.one eval_list_s (get_mon mon)
  
end

module Make ( Co : Sigs.Coefficient) ( Va : Sigs.Var) = struct

  module C = Co

  module V = Va

  module M = MakeMon(C)(V)

  type monic_mon = M.monic_mon

  type mon = M.mon

  type poly = {
    mons : (M.monic_mon, C.coef) BatHashtbl.t;
    mutable vars : V.S.set option
  }
  
  let divide_mon = M.divide_mon

  let mult_mon = M.mult_mon

  let zero_mon = M.zero

  let lcm_of_mon = M.lcm_of_mon

  let id_to_mon = M.id_to_mon

  let mon_to_id = M.mon_to_id

  let make_poly_from_mon (m : M.mon) : poly = 
    if M.is_zero m then {mons = BatHashtbl.create 20; vars = Some V.S.empty}
    else
      let coefs = BatHashtbl.create 20 in
      BatHashtbl.add coefs (snd m) (fst m);
      {mons = coefs; vars = Some (M.get_vars (snd m))}

  let make_mon_from_coef = M.make_mon_from_coef

  let make_mon_from_var = M.make_mon_from_var

  let make_mon_from_faugere_mon = M.make_mon_from_faugere_mon

  let from_var s : poly = make_poly_from_mon (M.make_mon_from_var s 1)

  let from_var_s s : poly = from_var (V.of_string s)

  let from_const c : poly = make_poly_from_mon (M.make_mon_from_coef c)

  let from_const_s s = from_const (C.from_string_c s)

  let from_var_pow s e : poly = make_poly_from_mon (M.make_mon_from_var s e)

  let from_var_s_pow s e : poly = from_var_pow (V.of_string s) e

  let negate (p : poly) : poly = 
    {p with mons = BatHashtbl.map (fun _ c -> C.mulc c (C.from_string_c "-1")) p.mons}

  let get_degree : V.t -> M.monic_mon -> int = M.degree

  let get_vars_m : monic_mon -> V.S.set = M.get_vars

  let get_mons (p : poly) : M.mon list = (List.map (fun (b, a) -> (a, b)) (BatHashtbl.to_list p.mons))

  let get_vars (p : poly) = 
    match p.vars with
    | Some vset -> vset
    | None -> List.fold_left (fun acc (_, m) -> V.S.union (M.get_vars m) acc) V.S.empty (get_mons p)
  
  (*let collect_terms (mons : poly) : poly = 
    let collected_terms = BatEnum.group_by (fun x y -> !M.ord (snd x) (snd y) = 0) mons in
    let res_with_0 = BatEnum.map 
      (fun terms -> 
        let reducer a b =
          match M.add_mon a b with
          | Some r -> r
          | None -> failwith "BatEnum didn't collect common terms"
        in
        BatEnum.reduce reducer terms
        ) collected_terms
    in
    let without_0 = BatEnum.filter (fun x -> not (M.is_zero x)) res_with_0 in
    if BatEnum.is_empty without_0 then BatEnum.singleton M.zero
    else without_0*)

  let mon_order (ac, am) (bc, bm) = 
    let mon_cmp = !M.ord am bm in
    if mon_cmp = 0 then C.cmp ac bc
    else mon_cmp

  (*let normalize poly = 
    let coefs = poly.coefs in
    let monicsl = fst (List.split (BatHashtbl.to_list poly.coefs)) in
    let monics = List.fold_left (fun tree m -> Base.Avltree.add tree ~replace:true ~compare:!M.ord ~added:(ref true) ~key:m ~data:0) (Base.Avltree.empty) monicsl in
    {coefs; monics}*)

  let from_mon_list (l : M.mon list) : poly = 
    let folder (acc, accset) (c, m) = 
      let vset = M.get_vars m in
      BatHashtbl.add acc m c;
      (acc, V.S.union accset vset)
    in
    let coefs, vset = List.fold_left folder (BatHashtbl.create 20, V.S.empty) l in
    {mons = coefs; vars = Some vset}

  (*let lt (mons : poly) = 
    match Base.Avltree.first mons.monics with
    | None -> M.zero
    | Some (m, _) -> 
      BatHashtbl.find mons.coefs m, m*)
      

  (*let lm poly = M.get_monic_mon (lt poly)*)

  (*let lc poly = fst (lt poly)*)

  (*let monomial_to_string mon = 
    let (is_neg, mons) = mon_to_string mon in
    if is_neg then "-" ^ mons
    else mons*)
  
  let to_string (p : poly) = 
    if BatHashtbl.is_empty p.mons then "0"
    else
      let folder (acc, first) (is_neg, m_s) =
        if first && is_neg then "-" ^ m_s, false
        else if first then m_s, false
        else if is_neg then acc ^ " - " ^ m_s, false
        else acc ^ " + " ^ m_s, false
      in
      let mon_list = List.rev (List.sort mon_order (get_mons p)) in
      fst (List.fold_left folder ("", true) (List.map M.mon_to_string mon_list))

  let ppm f m = 
    let (is_neg, mon_string) = M.mon_to_string m in
    let str = if is_neg then "-" ^ mon_string
      else mon_string
    in
    Format.pp_open_hbox f (); Format.pp_print_string f str; Format.pp_close_box f ()

  let ppmm f mm = Format.pp_open_hbox f (); Format.pp_print_string f (snd (M.mon_to_string (C.from_string_c "1", mm))); Format.pp_close_box f ()

  let pp ?(ord = !M.ord) f (p : poly) = 
    if BatHashtbl.is_empty p.mons then (Format.pp_open_hbox f (); Format.pp_print_string f "0"; Format.pp_close_box f ())
    else
      (
      let mon_list = List.rev (List.sort (fun a b -> ord (snd a) (snd b)) (get_mons p)) in
      Format.pp_open_box f 0;
      let first_mon = List.hd mon_list in
      let is_fm_neg, fm_str = M.mon_to_string first_mon in
      if is_fm_neg then Format.pp_print_string f ("-" ^ fm_str)
      else Format.pp_print_string f fm_str;
      let print_mon m = 
        let is_neg, m_str = M.mon_to_string m in
        if is_neg then (Format.pp_print_string f " -"; Format.pp_print_space f ())
        else (Format.pp_print_string f " +"; Format.pp_print_space f ());
        Format.pp_print_string f m_str
      in
      List.iter print_mon (List.tl mon_list);
      Format.pp_close_box f ()
      )

  let is_zero (p : poly) = 
    if BatHashtbl.length p.mons = 0 then true
    else
      let mons = get_mons p in
      List.for_all M.is_zero mons

  let is_one (p : poly) = 
    if BatHashtbl.length p.mons = 0 then false
    else
      List.for_all M.is_one (get_mons p)

  let is_const (p : poly) = 
    if BatHashtbl.length p.mons = 0 then Some (C.zero)
    else
      let mons = get_mons p in
      let folder const (c, mon) = 
        if M.is_const (c, mon) then 
          match const with
          | None -> None
          | Some c2 -> Some (C.addc c c2)
        else None
      in
      List.fold_left folder (Some (C.zero)) mons

  let add_mon (p : poly) ((c1, m) : M.mon)  =
    BatHashtbl.modify_def (C.zero) m (fun c2 -> C.addc c1 c2) p.mons;
    if C.cmp (BatHashtbl.find p.mons m) (C.zero) = 0 then BatHashtbl.remove p.mons m; p.vars <- None

  let subtract_mon (p : poly) ((c1, m) : M.mon) =
    BatHashtbl.modify_def (C.zero) m (fun c2 -> C.addc c2 (C.mulc (C.from_string_c "-1") c1)) p.mons;
    if C.cmp (BatHashtbl.find p.mons m) (C.zero) = 0 then BatHashtbl.remove p.mons m; p.vars <- None

  let addi (p1 : poly) (p2 : poly) = 
    let iterator m2 c2 = 
      add_mon p1 (c2, m2)
    in
    BatHashtbl.iter iterator p2.mons

  let add (p1 : poly) (p2 : poly) : poly = 
    let p1c = {mons = BatHashtbl.copy p1.mons; vars = p1.vars} in
    addi p1c p2;
    p1c
        
  let subtracti (p1 : poly) (p2 : poly) = 
    let iterator m2 c2 = 
      subtract_mon p1 (c2, m2)
    in
    BatHashtbl.iter iterator p2.mons;
    p1.vars <- None

  let subtract (p1 : poly) (p2 : poly) : poly =
    let p1c = {mons = BatHashtbl.copy p1.mons; vars = p1.vars} in
    subtracti p1c p2;
    p1c
  
  let mult_mon_poly mon (p : poly) : poly = 
    if M.is_zero mon then {mons = BatHashtbl.create 20; vars = Some (V.S.empty)}
    else 
      let p_enum = BatHashtbl.enum p.mons in
      let new_enums = BatEnum.map
        (fun (m, c) -> 
          let new_c, new_m = M.mult_mon mon (c, m) in
          new_m, new_c
        ) p_enum in
      match p.vars with
      | None -> {mons = BatHashtbl.of_enum new_enums; vars = None}
      | Some vset -> {mons = BatHashtbl.of_enum new_enums; vars = Some (V.S.union (M.get_vars (snd mon)) vset)}


  (*let mult_n (N (Sum p1)) (N (Sum p2)) = 
    let folder acc p2_mon = 
      add_n acc (N (Sum (List.map (fun x -> M.mult_mon p2_mon x) p1)))
    in
    List.fold_left folder (N (Sum[Coef (C.zero), Prod[]])) p2*)


  let mul (p1 : poly) (p2 : poly) : poly = 
    let acc = match p1.vars, p2.vars with
              | Some p1vs, Some p2vs -> {mons = BatHashtbl.create ((BatHashtbl.length p1.mons) * (BatHashtbl.length p2.mons)); vars = Some (V.S.union p1vs p2vs)}
              | _ -> {mons = BatHashtbl.create ((BatHashtbl.length p1.mons) * (BatHashtbl.length p2.mons)); vars = None}
    in
    let iterator p2_mon p2_c = 
      let monprod = mult_mon_poly (p2_c, p2_mon) p1 in
      addi acc monprod;
    in
    BatHashtbl.iter iterator p2.mons;
    acc



  let exp_poly p e =
    let rec aux curr_e acc = 
      if curr_e <= 0 then acc
      else aux (curr_e - 1) (mul p acc)
    in
    aux (e - 1) p

  let substitute_mon (var, p1) mon =
    let d = M.degree var (snd mon) in
    if d = 0 then make_poly_from_mon mon
    else
      match M.divide_mon mon (M.make_mon_from_var var d) with
      | Some rest_mon -> mul (exp_poly p1 d) (make_poly_from_mon rest_mon)
      | None -> failwith "Impossible"
      

  let substitute (var, p1) (p2 : poly) : poly =
    let acc = match p1.vars, p2.vars with 
              | Some p1vs, Some p2vs when V.S.mem var p2vs -> {mons = BatHashtbl.create 20; vars = Some (V.S.union (V.S.diff p2vs (V.S.add var V.S.empty)) p1vs)}
              | _ -> {mons = BatHashtbl.create 20; vars = None}
    in
    let iterator p2m p2c = 
      let new_p = substitute_mon (var, p1) (p2c, p2m) in
      addi acc new_p
    in
    BatHashtbl.iter iterator p2.mons;
    acc
    

  let compare p1 p2 = 
    let p1s = List.sort mon_order (get_mons p1) in
    let p2s = List.sort mon_order (get_mons p2) in
    BatEnum.compare mon_order (BatList.enum p1s) (BatList.enum p2s)

  let equal (p1 : poly) (p2 : poly) = is_zero (subtract p1 p2)
  
  let lex_ord = M.lex_ord

  let grlex_ord = M.grlex_ord

  type sorted_poly = poly * M.monic_mon list

  let make_sorted_poly (ord : M.monic_mon -> M.monic_mon -> int) p : sorted_poly = 
    let monics = List.map snd (get_mons p) in
    let sorted_monics = List.rev (List.sort ord monics) in
    (p, sorted_monics)

  let lt ((p, mons) : sorted_poly) = 
    if List.length mons = 0 then M.zero
    else 
      match BatHashtbl.find_option p.mons (List.hd mons) with
      | Some c -> c, List.hd mons
      | None ->
        failwith "Found a mon not in tbl"

  let lc p = fst (lt p)

  let get_poly = fst

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
        let ltdiv fi = divide_mon ltp (lt fi) in
        match find_map ltdiv divisors with
        | None ->
          subtract_mon (fst p) ltp;
          let new_pmons = List.tl (snd p) in
          add_mon (fst r) ltp;
          aux (fst p, new_pmons) mults (fst r, (snd r) @ [snd ltp])
        | Some (new_mon, i) ->
          reduction_occurred := true;
          subtracti (fst p) (mult_mon_poly new_mon (fst (List.nth divisors i)));
          List.iteri (fun j x -> if j = i then add_mon x new_mon) mults;
          aux (make_sorted_poly ord (fst p)) mults r
    in
    (!reduction_occurred, aux f (List.map (fun _ -> (make_poly_from_mon M.zero)) divisors) ((make_poly_from_mon M.zero), []))

  let make_monic ((p, ml) : sorted_poly) : sorted_poly = 
    let lc = lc (p, ml) in
    BatHashtbl.map_inplace (fun _ c -> C.divc c lc) p.mons;
    p, ml


  let compare_sorted (ord : monic_mon -> monic_mon -> int) ((p1, mon_list1) : sorted_poly) ((p2, mon_list2) : sorted_poly)= 
    let rec aux ml1 ml2 = 
      match ml1, ml2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | m1 :: m1s, m2 :: m2s ->
        let cmp_res = ord m1 m2 in
        if cmp_res <> 0 then cmp_res
        else
          let m1c, m2c = BatHashtbl.find p1.mons m1, BatHashtbl.find p2.mons m2 in
          let coef_cmp = C.cmp m1c m2c in
          if coef_cmp <> 0 then coef_cmp
          else aux m1s m2s
    in
    aux mon_list1 mon_list2
  
  let equal_sorted_sets b1 b2 = 
    let b1ss, b2ss = List.sort (compare_sorted lex_ord) b1, List.sort (compare_sorted lex_ord) b2 in
    let rec eq (p1, p1l) (p2, p2l) = 
      match p1l, p2l with
      | [], [] -> true
      | [], _ -> false
      | _, [] -> false
      | p1m :: p1ls, p2m :: p2ls ->
        if p1m = p2m then 
          let p1c, p2c = BatHashtbl.find p1.mons p1m, BatHashtbl.find p2.mons p2m in
          let coef_cmp = C.cmp p1c p2c in
          if coef_cmp <> 0 then false
          else eq (p1, p1ls) (p2, p2ls)
        else false
    in
    let eqs = List.map2 eq b1ss b2ss in
    List.for_all (fun x -> x) eqs

end
