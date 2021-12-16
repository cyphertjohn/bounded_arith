
module MakeMon (C : Sigs.Coefficient) = struct

  include C

  type monic_mon = (string * int) list

  type mon = coef * monic_mon

  let zero_mon = []

  let make_mon_from_coef c = (c, zero_mon)

  let make_mon_from_var s i : mon = (from_string_c "1", [(s, i)])

  let mon_from_coef c = (C.from_string_c c, zero_mon)

  let make_mon_from_faugere_mon vars (c, elist) : mon = 
    let folder acc v e = 
      if e > 0 then 
        (v, e) :: acc
      else acc
    in
    let monic = List.sort (fun (av, _) (bv, _)-> compare av bv)(List.fold_left2 folder [] vars elist) in
    C.of_zarith c, monic

  let zero = mon_from_coef "0"

  let minus_1 = mon_from_coef "-1"

  let is_zero (c, m) = 
    if C.is_zero c then
      if m = [] then true
      else failwith "Monomial has zero coefficient but is not empty"
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
    

  let mult_mon (a : mon) (b : mon) : mon = 
    let new_coef = C.mulc (fst a) (fst b) in
    if (C.is_zero new_coef) then zero
    else 
      let rec zip acc am bm = 
        match am, bm with
        | [], [] -> List.rev acc
        | _ :: _ , [] -> (List.rev acc) @ am
        | [], _ :: _ -> (List.rev acc) @ bm
        | (av, ae) :: a_rest, (bv, be) :: b_rest ->
          if av = bv then
            zip ((av, ae + be) :: acc) a_rest b_rest
          else if av < bv then
            zip ((av, ae) :: acc) a_rest bm
          else
            zip ((bv, be) :: acc) am b_rest
        in
      (new_coef, zip [] (snd a) (snd b))
  
  let divide_mon (a : mon) (b : mon) : mon option = 
    let b_coef = fst b in
    if C.is_zero b_coef then failwith "Divide by 0";
    let new_coef = C.divc (fst a) (fst b) in
    let blist = snd b in
    let alist = snd a in
    let rec var_divide rema remb acc =
      match (rema, remb) with
      | [], [] -> Some (List.rev acc)
      | [], _ :: _ -> None
      | _, [] -> Some ((List.rev acc) @ rema)
      | (av, ae) :: remas, (bv, be) :: rembs ->
        if av = bv && ae = be then var_divide remas rembs acc
        else if av = bv && ae > be then var_divide remas rembs (((av, ae - be)) :: acc)
        else if av = bv && ae < be then None
        else if av < bv then var_divide remas remb (((av, ae)) :: acc)
        else None
    in
    match (var_divide alist blist []) with
    | None -> None
    | Some new_mon -> Some (new_coef, new_mon)
  
  let lcm_of_mon (a : monic_mon) (b : monic_mon) : monic_mon = 
    let rec aux x y acc =
      match (x, y) with
      | ([], _) -> y @ acc
      | (_, []) -> x @ acc
      | ((xvar, e1) :: xs, (yvar, e2) :: ys) -> 
        if xvar = yvar then (xvar, max e1 e2) :: (aux xs ys acc)
        else if xvar < yvar then (xvar, e1) :: (aux xs y acc)
        else (yvar, e2) :: (aux ys x acc)
    in
    (aux a b [])

  let degree v (m : monic_mon) = 
    match List.find_opt (fun (var, _) -> v = var) m with
    | Some (_, d) -> d
    | None -> 0

  let get_vars (m : monic_mon) = 
    BatList.enum (List.map fst m)

  let monic_mon_to_string (m : monic_mon) = 
    let folder acc (v, e) = 
      if e > 1 then (v ^ "^" ^ (string_of_int e)) :: acc
      else v :: acc
    in
    String.concat "" (List.rev (List.fold_left folder [] m))

  let mon_to_string (c, m) =
    let is_neg, norm_c = 
      if cmp c (from_string_c "0") < 0 then true, (mulc c (from_string_c "-1"))
      else false, c
    in
    if m = [] then is_neg, to_string_c norm_c
    else if is_one norm_c then is_neg, (monic_mon_to_string m)
    else is_neg, (to_string_c norm_c) ^ (monic_mon_to_string m)

  let is_const ((_, m) : mon) = m = []

  let rec lex_ord a b = 
    match (a, b) with
    | ([], []) -> 0
    | ([], _ :: _) -> -1
    | (_ :: _, []) -> 1
    | ((xv, xe) :: xs, (yv, ye) :: ys) -> 
      if xv = yv then 
        if compare xe ye = 0 then lex_ord xs ys
        else compare xe ye
      else if xv < yv then 1
      else (-1)

  let total_deg (m : monic_mon) = 
    List.fold_left (fun acc (_, e) -> e + acc) 0 m


  let grlex_ord (a : monic_mon) (b : monic_mon) = 
    let a_deg = total_deg a in
    let b_deg = total_deg b in
    if compare a_deg b_deg = 0 then lex_ord a b
    else compare a_deg b_deg

  let ord = ref lex_ord

  let mon_ord (c1, m1) (c2, m2) = 
    let order = !ord m1 m2 in
    if order = 0 then C.cmp c1 c2 else order
  
end
module MakeP (M : sig
              include Sigs.Coefficient
              type monic_mon
              type mon = coef * monic_mon
              val make_mon_from_faugere_mon : string list -> Z.t * (int list) -> mon
              val make_mon_from_coef : coef -> mon
              val make_mon_from_var : string -> int -> mon
              val is_zero : mon -> bool
              val zero : mon
              val ord : (monic_mon -> monic_mon -> int) ref
              val minus_1 : mon
              (*val add_mon : mon -> mon -> mon option*)
              val mult_mon : mon -> mon -> mon
              val divide_mon : mon -> mon -> mon option
              val lcm_of_mon : monic_mon -> monic_mon -> monic_mon
              val degree : string -> monic_mon -> int
              val total_deg : monic_mon -> int
              val get_vars : monic_mon -> string BatEnum.t
              val mon_to_string : mon -> bool * string
              val is_const : mon -> bool
              val lex_ord : monic_mon -> monic_mon -> int
              val grlex_ord : monic_mon -> monic_mon -> int
            end ) = struct

  let set_ord order = M.ord := order

  module Mon = M

  type poly = (M.monic_mon, M.coef) BatHashtbl.t

  let make_poly_from_mon (m : M.mon) : poly = 
    if M.is_zero m then BatHashtbl.create 20
    else
      let coefs = BatHashtbl.create 20 in
      BatHashtbl.add coefs (snd m) (fst m);
      coefs

  let from_var s : poly = make_poly_from_mon (M.make_mon_from_var s 1)

  let from_const c : poly = make_poly_from_mon (M.make_mon_from_coef c)

  let from_const_s s = from_const (M.from_string_c s)

  let from_var_pow s e : poly = make_poly_from_mon (M.make_mon_from_var s e)

  let negate (mons : poly) = 
    BatHashtbl.map (fun _ c -> M.mulc c (M.from_string_c "-1")) mons

  let get_degree = M.degree

  let get_vars_m = M.get_vars

  let get_mons (mons : poly) : M.mon BatEnum.t = BatEnum.map (fun (a, b) -> (b, a)) (BatHashtbl.enum mons)

  let get_vars (mons : poly) = 
    let with_dups = BatEnum.concat (BatEnum.map (fun (m, _) -> M.get_vars m) (BatHashtbl.enum mons)) in
    BatEnum.uniq with_dups
  
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
    if mon_cmp = 0 then M.cmp ac bc
    else mon_cmp

  (*let normalize poly = 
    let coefs = poly.coefs in
    let monicsl = fst (List.split (BatHashtbl.to_list poly.coefs)) in
    let monics = List.fold_left (fun tree m -> Base.Avltree.add tree ~replace:true ~compare:!M.ord ~added:(ref true) ~key:m ~data:0) (Base.Avltree.empty) monicsl in
    {coefs; monics}*)

  let from_mon_list (l : M.mon list) : poly = 
    let folder acc (c, m) = 
      BatHashtbl.add acc m c;
      acc
    in
    let coefs = List.fold_left folder (BatHashtbl.create 20) l in
    coefs

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
    if BatHashtbl.is_empty p then "0"
    else
      let folder (acc, first) (is_neg, m_s) =
        if first && is_neg then "-" ^ m_s, false
        else if first then m_s, false
        else if is_neg then acc ^ " - " ^ m_s, false
        else acc ^ " + " ^ m_s, false
      in
      let mon_list = List.rev (List.sort mon_order (List.map (fun (a, b) -> (b, a)) (BatHashtbl.to_list p))) in
      fst (List.fold_left folder ("", true) (List.map M.mon_to_string mon_list))

  let ppm f m = 
    let (is_neg, mon_string) = M.mon_to_string m in
    let str = if is_neg then "-" ^ mon_string
      else mon_string
    in
    Format.pp_open_hbox f (); Format.pp_print_string f str; Format.pp_close_box f ()

  let ppmm f mm = Format.pp_open_hbox f (); Format.pp_print_string f (snd (M.mon_to_string (M.from_string_c "1", mm))); Format.pp_close_box f ()

  let pp ?(ord = !M.ord) f p = 
    if BatHashtbl.is_empty p then (Format.pp_open_hbox f (); Format.pp_print_string f "0"; Format.pp_close_box f ())
    else
      (
      let mon_list = List.rev (List.map (fun (b, a) -> (a, b)) (List.sort (fun a b -> ord (fst a) (fst b)) (BatHashtbl.to_list p))) in
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
    if BatHashtbl.length p = 0 then true
    else
      let mons = get_mons p in
      BatEnum.for_all M.is_zero mons

  let is_const (p : poly) = 
    if BatHashtbl.length p = 0 then true
    else
      let mons = get_mons p in
      BatEnum.for_all M.is_const mons

  let add_mon (p : poly) ((c1, m) : M.mon)  =
    BatHashtbl.modify_def (M.from_string_c "0") m (fun c2 -> M.addc c1 c2) p;
    if M.cmp (BatHashtbl.find p m) (M.from_string_c "0") = 0 then BatHashtbl.remove p m

  let subtract_mon (p : poly) ((c1, m) : M.mon)  =
    BatHashtbl.modify_def (M.from_string_c "0") m (fun c2 -> M.addc c1 (M.mulc (M.from_string_c "-1") c2)) p;
    if M.cmp (BatHashtbl.find p m) (M.from_string_c "0") = 0 then BatHashtbl.remove p m

  let addi (p1 : poly) (p2 : poly) = 
    let iterator m2 c2 = 
      add_mon p1 (c2, m2)
    in
    BatHashtbl.iter iterator p2

  let add (p1 : poly) (p2 : poly) : poly = 
    let p1c = BatHashtbl.copy p1 in
    addi p1c p2;
    p1c
        
  let mult_mon_poly mon (p : poly) : poly = 
    if M.is_zero mon then BatHashtbl.create 20
    else 
      let p_enum = BatHashtbl.enum p in
      let new_enums = BatEnum.map
        (fun (m, c) -> 
          let new_c, new_m = M.mult_mon mon (c, m) in
          new_m, new_c
        ) p_enum in
      BatHashtbl.of_enum new_enums


  (*let mult_n (N (Sum p1)) (N (Sum p2)) = 
    let folder acc p2_mon = 
      add_n acc (N (Sum (List.map (fun x -> M.mult_mon p2_mon x) p1)))
    in
    List.fold_left folder (N (Sum[Coef (M.from_string_c "0"), Prod[]])) p2*)


  let mul (p1 : poly) (p2 : poly) : poly = 
    let acc = BatHashtbl.create ((BatHashtbl.length p1) * (BatHashtbl.length p2)) in
    let iterator p2_mon p2_c = 
      let monprod = mult_mon_poly (p2_c, p2_mon) p1 in
      addi acc monprod;
    in
    BatHashtbl.iter iterator p2;
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
      

  let substitute (var, p1) (p2 : poly) =
    let acc = BatHashtbl.create 20 in 
    let iterator p2m p2c = 
      let new_p = substitute_mon (var, p1) (p2c, p2m) in
      addi acc new_p
    in
    BatHashtbl.iter iterator p2;
    acc
    

  let compare p1 p2 = 
    let p1s = List.sort mon_order (List.map (fun (a, b) -> (b, a)) (BatHashtbl.to_list p1)) in
    let p2s = List.sort mon_order (List.map (fun (a, b) -> (b, a)) (BatHashtbl.to_list p2)) in
    BatEnum.compare mon_order (BatList.enum p1s) (BatList.enum p2s)

  let equal (p1 : poly) (p2 : poly) = 
    if BatHashtbl.length p1 = BatHashtbl.length p2 then 
      let rec aux curr_p2 = 
        match BatEnum.get curr_p2 with
        | None -> true
        | Some (m, c2) ->
          match BatHashtbl.find_option p1 m with
          | None -> false
          | Some c1 ->
            if M.cmp c1 c2 = 0 then aux curr_p2
            else false
      in
      aux (BatHashtbl.enum p2)
    else false


  let subtract p1_n p2_n = 
    let neg_p2_n = mult_mon_poly M.minus_1 p2_n in
    addi p1_n neg_p2_n
  
  let lex_ord = M.lex_ord

  let grlex_ord = M.grlex_ord

end

module Make ( C : Sigs.Coefficient) = MakeP(MakeMon(C))
