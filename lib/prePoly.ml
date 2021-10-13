module MakeMon (C : Sigs.Coefficient) = struct
                  
  include C

  type var_power = Exp of string * int

  type monic_mon = Prod of var_power list

  let get_deg (Exp (_, e)) = e

  let cmp_var (Exp(x, e1)) (Exp(y, e2)) = if compare x y = 0 then compare e1 e2 else -1 * (compare x y)
                 
  let sort_monic_mon (Prod l) = 
    let remove_one = List.filter (fun (Exp(_, e)) -> e <> 0) l in
    Prod (List.rev (List.sort cmp_var remove_one))

  let rec lex_ord a b = 
    match (a, b) with
    | (Prod [], Prod []) -> 0
    | (Prod [], _) -> -1
    | (_, Prod []) -> 1
    | (Prod (x :: xs), Prod (y :: ys)) -> if cmp_var x y = 0 then lex_ord (Prod xs) (Prod ys)
                                          else cmp_var x y
  
  let total_deg (Prod m) = List.fold_left (+) 0 (List.map get_deg m)
  
  let grlex_ord a b =
    if compare (total_deg a) (total_deg b) = 0 then lex_ord a b
    else compare (total_deg a) (total_deg b)

  

  let sort_monomial (coef, mon) = (coef, sort_monic_mon mon)

  type mon = coef * monic_mon

  let zero = C.from_string_c "0", Prod []

  let minus_1 = C.from_string_c "-1", Prod []

  let is_zero (c, _) = C.is_zero c

  let make_mon_from_coef c = c, Prod []

  let make_mon_from_var v d = C.from_string_c "1", Prod[Exp(v, d)]
  

  let add_mon a b = 
    if is_zero a then Some b
    else if is_zero b then Some a
    else
      let (ac, amon), (bc, bmon) = (a, b) in
      if amon = bmon then 
        let c = C.addc ac bc in
        if C.is_zero c then Some zero
        else Some ((C.addc ac bc), amon)
      else None
    

  let mult_mon a b = 
    let new_coef = C.mulc (fst a) (fst b) in
    if (C.is_zero new_coef) then new_coef, Prod []
    else 
      let (Prod l1, Prod l2) = (snd a, snd b) in
      let rec zip m1 m2 acc =
        match (m1, m2) with 
        | ([], []) -> (new_coef, Prod (List.rev acc))
        | (_, []) -> (new_coef, Prod ((List.rev acc) @ m1))
        | ([], _) -> (new_coef, Prod ((List.rev acc) @ m2))
        | ((Exp (x, e1)) :: xs, Exp (y, e2) :: ys) -> 
          if x = y then zip xs ys ((Exp (y, e1+e2)) :: acc)
          else if compare x y < 0 then zip xs m2 ((Exp (x, e1)) :: acc)
          else zip m1 ys ((Exp (y, e2)) :: acc)
      in
      zip l1 l2 []


  let divide_mon a b = 
    let b_coef = fst b in
    if C.is_zero b_coef then failwith "Divide by 0";
    let new_coef = C.divc (fst a) (fst b) in
    let (Prod vars) = snd b in
    let (Prod alist) = snd a in
    let rec var_divide rema remb acc =
      match (rema, remb) with
      | [], [] -> Some (List.rev acc)
      | [], _ :: _ -> None
      | _, [] -> Some ((List.rev acc) @ rema)
      | Exp(av, ae) :: remas, Exp (bv, be) :: rembs ->
        if av = bv && ae = be then var_divide remas rembs acc
        else if av = bv && ae > be then var_divide remas rembs ((Exp (av, ae - be)) :: acc)
        else if av = bv && ae < be then None
        else if av < bv then var_divide remas remb ((Exp(av, ae)) :: acc)
        else None
    in
    match (var_divide alist vars []) with
    | None -> None
    | Some new_mon -> Some (new_coef, Prod new_mon)
  
  let lcm_of_mon (Prod a) (Prod b) = 
    let rec aux x y acc =
      match (x, y) with
      | ([], _) -> y @ acc
      | (_, []) -> x @ acc
      | (Exp(xvar, e1) :: xs, Exp(yvar, e2) :: ys) -> 
        if xvar = yvar then Exp(xvar, max e1 e2) :: (aux xs ys acc)
        else if xvar < yvar then Exp(xvar, e1) :: (aux xs y acc)
        else Exp(yvar, e2) :: (aux ys x acc)
    in
    Prod (aux a b [])


  let ord = ref lex_ord

  let degree v (Prod l) = 
    let var_exp = List.find_opt (fun (Exp (x, _)) -> v = x) l in
    match var_exp with
    | None -> 0
    | Some (Exp (_, d)) -> d
    
  let get_vars (Prod l) = 
    let folder acc (Exp (v, _)) = 
      if List.mem v acc then acc
      else v :: acc
    in
    List.fold_left folder [] l

  let var_power_to_string (Exp(x, e)) = if e > 1 then x ^ "^" ^ (string_of_int e) else x
  let monic_mon_to_string m = String.concat "" (List.map var_power_to_string (let Prod l = m in l))

  let mon_to_string (c, Prod m) =
    let is_neg, norm_c = 
      if cmp c (from_string_c "0") < 0 then true, (mulc c (from_string_c "-1"))
      else false, c
    in
    if m = [] then is_neg, to_string_c norm_c
    else if is_one norm_c then is_neg, (monic_mon_to_string (Prod m))
    else is_neg, (to_string_c norm_c) ^ (monic_mon_to_string (Prod m)) 
  
end


module MakeP (M : sig
              include Sigs.Coefficient
              type monic_mon
              type mon = coef * monic_mon
              val make_mon_from_coef : coef -> mon
              val make_mon_from_var : string -> int -> mon
              val is_zero : mon -> bool
              val zero : mon
              val ord : (monic_mon -> monic_mon -> int) ref
              val minus_1 : mon
              val add_mon : mon -> mon -> mon option
              val mult_mon : mon -> mon -> mon
              val divide_mon : mon -> mon -> mon option
              val lcm_of_mon : monic_mon -> monic_mon -> monic_mon
              val degree : string -> monic_mon -> int
              val get_vars : monic_mon -> string list
              val mon_to_string : mon -> bool * string
            end ) = struct

  let set_ord order = M.ord := order

  type poly = NSum of (M.mon list)

  module M = M

  let from_var s = NSum [M.make_mon_from_var s 1]

  let from_const c = NSum [M.make_mon_from_coef c]

  let from_const_s s = from_const (M.from_string_c s)

  let from_var_pow s e = NSum [M.make_mon_from_var s e]

  let negate (NSum mons) = NSum (List.map (fun m -> M.mult_mon m (M.minus_1)) mons)

  let get_degree = M.degree

  let get_vars_m = M.get_vars

  let get_mons (NSum l) = l

  let get_vars (NSum poly) = 
    let with_dups = List.concat (List.map (fun (_, m) -> M.get_vars m) poly) in
    let uniq_cons xs x = if List.mem x xs then xs else x :: xs in
    let remove_dups xs = List.fold_left uniq_cons [] xs in
    remove_dups with_dups

  
  let collect_terms_normal (NSum sorted) = 
    if List.length sorted = 0 then NSum [M.zero]
    else
      let folder (acc, prev_m) curr_m =
        match (M.add_mon prev_m curr_m) with
        | Some res-> 
          (acc, res)
        | _ ->
          (prev_m :: acc, curr_m)
      in
      let (monomials, last) = List.fold_left folder ([], M.zero) sorted in
      let res_with_0 = List.rev (last :: monomials) in
      let without_0 = List.filter (fun x -> not (M.is_zero x)) res_with_0 in
      if List.length without_0 = 0 then NSum [M.zero]
      else NSum (without_0)

  let mon_order (ac, am) (bc, bm) = 
    let mon_cmp = !M.ord am bm in
    if mon_cmp = 0 then M.cmp ac bc
    else mon_cmp

  let normalize (NSum poly) = 
    collect_terms_normal (NSum (List.rev (List.sort mon_order poly)))

  let from_mons l = normalize (NSum l)

  let lt (NSum poly) = List.hd poly

  let is_zero p = 
    M.is_zero (lt p)

  (*let lm poly = M.get_monic_mon (lt poly)*)

  let lc poly = fst (lt poly)

  (*let monomial_to_string mon = 
    let (is_neg, mons) = mon_to_string mon in
    if is_neg then "-" ^ mons
    else mons*)
  
  let to_string (NSum p) = 
    let folder (acc, first) (is_neg, m_s) =
      if first && is_neg then "-" ^ m_s, false
      else if first then m_s, false
      else if is_neg then acc ^ " - " ^ m_s, false
      else acc ^ " + " ^ m_s, false
    in
    fst (List.fold_left folder ("", true) (List.map M.mon_to_string p))

  let ppm f m = Format.pp_print_string f (to_string (NSum [m]))

  let ppmm f mm = Format.pp_print_string f (snd (M.mon_to_string (M.from_string_c "1", mm)))

  let pp f p = Format.pp_print_string f (to_string p)

(*  let add_mon (Coef c1, m) (Sum a) =
    if a = [] then Sum [(Coef c1, m)]
    else if (List.exists (fun (Coef _, m2) -> !ord m m2 = 0) a) then
      Sum (List.map (fun (Coef c2, m2) -> if !ord m m2 = 0 then (Coef (c1 +. c2), m) else (Coef c2, m2)) a)
    else Sum ((Coef c1, m) :: a) *)

  let add (NSum p1) (NSum p2) = 
    let rec zip a b acc =
      match (a, b) with
      | ([], []) -> NSum (List.rev acc)
      | (_, []) -> NSum ((List.rev acc) @ a)
      | ([], _) -> NSum ((List.rev acc) @ b)
      | (m1 :: xs, m2 :: ys) ->
        (match (M.add_mon m1 m2) with
        | Some res ->
          if M.is_zero res then zip xs ys acc
          else zip xs ys (res :: acc)
        | None ->
          if mon_order m1 m2 > 0 then zip xs b (m1 :: acc)
          else zip a ys (m2 :: acc))
    in
    let (NSum temp_res) = zip p1 p2 [] in
    if List.length temp_res = 0 then NSum [M.zero]
    else (NSum temp_res)
  

  let mult_mon_poly mon (NSum p2) = NSum (List.map (M.mult_mon mon) p2)

  (*let mult_n (N (Sum p1)) (N (Sum p2)) = 
    let folder acc p2_mon = 
      add_n acc (N (Sum (List.map (fun x -> M.mult_mon p2_mon x) p1)))
    in
    List.fold_left folder (N (Sum[Coef (M.from_string_c "0"), Prod[]])) p2*)


  let mul (NSum p1_norm) (NSum p2_norm) = 
    let folder acc p2_mon = 
      acc @ ((List.map (fun x -> M.mult_mon p2_mon x) p1_norm))
    in
    collect_terms_normal (NSum (List.fold_left folder [] p2_norm))



  let exp_poly p e =
    let rec aux curr_e acc = 
      if curr_e <= 0 then acc
      else aux (curr_e - 1) (mul p acc)
    in
    aux (e - 1) p

  let subsitute_mon (var, p1) mon =
    let d = M.degree var (snd mon) in
    if d = 0 then NSum [mon]
    else
      match M.divide_mon mon (M.make_mon_from_var var d) with
      | Some rest_mon -> mul (exp_poly p1 d) (NSum [rest_mon])
      | None -> failwith "Impossible"
      

  let substitute (var, p1) (NSum p2) = 
    let sub_list = List.map (subsitute_mon (var, p1)) p2 in
    List.fold_left (fun acc p -> add acc p) (List.hd sub_list) (List.tl sub_list)
    

  let compare (NSum p1) (NSum p2) = 
    let rec aux a b = 
      match (a, b) with 
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) -> 1
      | (x :: xs, y :: ys) -> if mon_order x y = 0 then aux xs ys else mon_order x y
    in
    aux p1 p2


  let subtract p1_n p2_n = 
    let neg_p2_n = mult_mon_poly M.minus_1 p2_n in
    add p1_n neg_p2_n
  
end

module Make ( C : Sigs.Coefficient) = MakeP(MakeMon(C))
