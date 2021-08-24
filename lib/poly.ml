open Sigs
open Sigs.Polynomial


let get_deg (Exp (_, e)) = e 
                  
let cmp_var (Exp(x, e1)) (Exp(y, e2)) = if compare x y = 0 then compare e1 e2 else -1 * (compare x y)
                 
let sort_monic_mon (Prod l) = 
  let remove_one = List.filter (fun (Exp(_, e)) -> e <> 0) l in
  Prod (List.rev (List.sort cmp_var remove_one))

let rec lex_ord a b = 
  match (sort_monic_mon a, sort_monic_mon b) with
  | (Prod [], Prod []) -> 0
  | (Prod [], _) -> -1
  | (_, Prod []) -> 1
  | (Prod (x :: xs), Prod (y :: ys)) -> if cmp_var x y = 0 then lex_ord (Prod xs) (Prod ys)
                          else cmp_var x y
  
let total_deg (Prod m) = List.fold_left (+) 0 (List.map get_deg m)
  
let grlex_ord a b =
  if compare (total_deg a) (total_deg b) = 0 then lex_ord a b
  else compare (total_deg a) (total_deg b)

module MakeMon (C : Coefficient) = struct

  include C
  
  let sort_monomial (coef, mon) = (coef, sort_monic_mon mon)
  
  let get_monic_mon (Coef _, mon) = mon
  
  let get_coef (Coef c, Prod _) = c

  let mult_mon a b = 
    let new_coef = C.mulc (get_coef a) (get_coef b) in
    if (C.is_zero new_coef) then (Coef (C.from_string_c "0"), Prod [])
    else 
      let (Prod l1, Prod l2) = (sort_monic_mon (get_monic_mon a), sort_monic_mon (get_monic_mon b)) in
      let rec zip m1 m2 acc =
        match (m1, m2) with 
        | ([], []) -> (Coef new_coef, Prod (List.rev acc))
        | (_, []) -> (Coef new_coef, Prod ((List.rev acc) @ m1))
        | ([], _) -> (Coef new_coef, Prod ((List.rev acc) @ m2))
        | ((Exp (x, e1)) :: xs, Exp (y, e2) :: ys) -> 
          if x = y then zip xs ys ((Exp (y, e1+e2)) :: acc)
          else if compare x y < 0 then zip xs m2 ((Exp (x, e1)) :: acc)
          else zip m1 ys ((Exp (y, e2)) :: acc)
      in
      zip l1 l2 []
  
  let divide_mon a b = 
    let b_coef = get_coef b in
    if C.is_zero b_coef then failwith "Divide by 0";
    let new_coef = C.divc (get_coef a) (get_coef b) in
    let (Prod vars) = get_monic_mon b in
    if vars = [] then Some (Coef new_coef, get_monic_mon a)
    else 
      let (Prod alist) = get_monic_mon a in
      let var_divide acc (Exp (bvar, be)) = 
        let (Exp (_, ae)) = List.find (fun (Exp (avar, _)) -> avar = bvar) acc in
        if ae >= be then List.map (fun (Exp (v, e)) -> if v = bvar then Exp (v, e - be) else Exp (v, e)) acc
        else raise Not_found
      in
      try
        Some (sort_monomial (Coef new_coef, Prod (List.fold_left var_divide alist vars)))
      with Not_found -> None
  
  let lcm (Prod a) (Prod b) = 
    let rec aux x y acc =
      match (x, y) with
      | ([], _) -> y @ acc
      | (_, []) -> x @ acc
      | (Exp(xvar, e1) :: xs, Exp(yvar, e2) :: ys) -> 
        if xvar = yvar then Exp(xvar, max e1 e2) :: (aux xs ys acc)
        else if xvar < yvar then Exp(xvar, e1) :: (aux xs y acc)
        else Exp(yvar, e2) :: (aux ys x acc)
    in
    sort_monic_mon (Prod (aux a b []))

  let ord = ref lex_ord

  let mon_ord (Coef c1, m1) (Coef c2, m2) = 
    let order = !ord m1 m2 in
    if order = 0 then C.cmp c1 c2 else order
  
end


module MakeP (M : sig
              include Coefficient
              val ord : (monic_mon -> monic_mon -> int) ref
              val mon_ord : coef monomial -> coef monomial -> int
              val mult_mon : coef monomial -> coef monomial -> coef monomial
              val sort_monomial : coef monomial -> coef monomial
              val get_monic_mon : 'a monomial -> monic_mon
              val divide_mon : coef monomial -> coef monomial -> (coef monomial) option
              val lcm : monic_mon -> monic_mon -> monic_mon
            end ) = struct

  let set_ord order = M.ord := order

  type normalized_poly = N of (M.coef polynomial)



  (*let sort_poly (Sum poly) = 
    let remove_zero = List.filter (fun (Coef c, _) -> not (M.is_zero c)) (List.map M.sort_monomial poly) in
    if remove_zero = [] then (Sum [(Coef (M.from_string_c "0"), Prod [])])
    else Sum (List.rev (List.sort M.mon_ord remove_zero))*)

  let zero = Sum [(Coef (M.from_string_c "0"), Prod [])]

  let is_zero_n (N p) = 
    match p with
     | (Sum [(Coef c, Prod [])]) when M.is_zero c -> true
     |_ -> false

  

  let collect_terms_normal (N (Sum sorted)) = 
    if List.length sorted = 0 then N (Sum [(Coef (M.from_string_c "0"), Prod [])])
    else
      let folder (acc, (prev_m : M.coef monomial)) (curr_m : M.coef monomial) =
        match (prev_m, curr_m) with
        | (Coef c1, m1), (Coef c2, m2) when m1 = m2 -> 
          (acc, (Coef (M.addc c1 c2), m1))
        | _ ->
          (prev_m :: acc, curr_m)
      in
      let (monomials, last) = List.fold_left folder ([], (Coef (M.from_string_c "0"), Prod [])) sorted in
      let res_with_0 = List.rev (last :: monomials) in
      let without_0 = List.filter (fun (Coef c, _) -> not (M.is_zero c)) res_with_0 in
      if List.length without_0 = 0 then N (zero)
      else N (Sum (without_0))

  let normalize (Sum poly) = 
    collect_terms_normal (N (Sum (List.rev (List.sort M.mon_ord (List.map M.sort_monomial poly)))))

  let unnormalize (N p) = p
    
  let is_zero p = 
    is_zero_n (normalize p)

  let lt (N (Sum poly)) = List.hd poly

  let lm poly = M.get_monic_mon (lt poly)

  let lc poly = let (Coef c, _) = lt poly in c

(*  let add_mon (Coef c1, m) (Sum a) =
    if a = [] then Sum [(Coef c1, m)]
    else if (List.exists (fun (Coef _, m2) -> !ord m m2 = 0) a) then
      Sum (List.map (fun (Coef c2, m2) -> if !ord m m2 = 0 then (Coef (c1 +. c2), m) else (Coef c2, m2)) a)
    else Sum ((Coef c1, m) :: a) *)

  let add_n (N (Sum p1)) (N (Sum p2)) = 
    let rec zip a b acc =
      match (a, b) with
      | ([], []) -> N (Sum (List.rev acc))
      | (_, []) -> N( Sum ((List.rev acc) @ a))
      | ([], _) -> N (Sum ((List.rev acc) @ b))
      | ((Coef c1, m1) :: xs, (Coef c2, m2) :: ys) when m1 = m2 ->
        if M.is_zero (M.addc c1 c2) then zip xs ys acc
        else zip xs ys ((Coef (M.addc c1 c2), m1) :: acc)
      | ((Coef c1, m1) :: xs, (Coef _, m2) :: _) when !M.ord m1 m2 > 0 ->
        zip xs b ((Coef c1, m1) :: acc)
      | (_, (Coef c2, m2) :: ys) ->
        zip a ys ((Coef c2, m2) :: acc)
    in
    let (N (Sum temp_res)) = zip p1 p2 [] in
    if List.length temp_res = 0 then N (zero)
    else (N (Sum temp_res))
  

  let mult_mon_poly mon (N (Sum p2)) = N (Sum (List.map (M.mult_mon mon) p2))

  (*let mult_n (N (Sum p1)) (N (Sum p2)) = 
    let folder acc p2_mon = 
      add_n acc (N (Sum (List.map (fun x -> M.mult_mon p2_mon x) p1)))
    in
    List.fold_left folder (N (Sum[Coef (M.from_string_c "0"), Prod[]])) p2*)

  let minus_1 = Sum [(Coef (M.from_string_c ("-1")), Prod [])]

  let subtract_n p1_n p2_n = 
    let neg_p2_n = mult_mon_poly (Coef (M.from_string_c ("-1")), Prod []) p2_n in
    add_n p1_n neg_p2_n

  let add (Sum p1) (Sum p2) = 
    Sum (p1 @ p2)

  let mult (Sum p1) (Sum p2) = 
    let folder acc p2_mon = 
      acc @ ((List.map (fun x -> M.mult_mon p2_mon x) p1))
    in
    Sum (List.fold_left folder [] p2)


  let var_power_to_string (Exp(x, e)) = if e > 1 then x ^ "^" ^ (string_of_int e) else x
  let monic_mon_to_string m = String.concat "" (List.map var_power_to_string (let Prod l = m in l))

  let mon_to_string mon =
    let (Coef c, Prod m) = M.sort_monomial mon in
    let is_neg, norm_c = 
      if M.cmp c (M.from_string_c "0") < 0 then true, (M.mulc c (M.from_string_c "-1"))
      else false, c
    in
    if m = [] then is_neg, M.to_string_c norm_c
    else if M.is_one norm_c then is_neg, (monic_mon_to_string (Prod m))
    else is_neg, (M.to_string_c norm_c) ^ (monic_mon_to_string (Prod m)) 

  let monomial_to_string mon = 
    let (is_neg, mons) = mon_to_string mon in
    if is_neg then "-" ^ mons
    else mons
  
  let to_string unnormal = 
    let (N (Sum p)) = normalize unnormal in
    let folder (acc, first) (is_neg, m_s) =
      if first && is_neg then "-" ^ m_s, false
      else if first then m_s, false
      else if is_neg then acc ^ " - " ^ m_s, false
      else acc ^ " + " ^ m_s, false
    in
    fst (List.fold_left folder ("", true) (List.map mon_to_string p))

  let exp_poly p e = (*TODO: optimize *)
    let rec aux curr_e acc = 
      if curr_e <= 0 then acc
      else aux (curr_e - 1) (mult p acc)
    in
    aux (e - 1) p

  let subsitute_mon (var, p1) (Coef c, Prod mon) =
    let (rest_mon, sub_mon) = 
      List.fold_left 
        (fun (seen_mon, found_opt) (Exp (v2, e)) ->
          if var = v2 then
            (seen_mon, Some (Exp (v2, e)))
          else
            ((Exp (v2, e)) :: seen_mon, found_opt)
        )
        ([], None)
        mon
    in
    match sub_mon with
    | None -> Sum [(Coef c, Prod mon)]
    | Some (Exp (_, e)) ->
      let expand_p1 = exp_poly p1 e in
      mult expand_p1 (Sum [(Coef c, Prod rest_mon)])
      

  let substitute (var, p1) (Sum p2) = 
    let sub_list = List.map (subsitute_mon (var, p1)) p2 in
    List.fold_left (fun acc p -> add acc p) (List.hd sub_list) (List.tl sub_list)
    

  let compare_n (N p1) (N p2) = 
    let rec aux (Sum a) (Sum b) = 
      match (a, b) with 
      | ([], []) -> 0
      | ([], _) -> -1
      | (_, []) -> 1
      | (x :: xs, y :: ys) -> if M.mon_ord x y = 0 then aux (Sum xs) (Sum ys) else M.mon_ord x y
    in
    aux p1 p2

  let compare p1 p2 = 
    compare_n (normalize p1) (normalize p2)

  let string_to_coef (Sum l) = 
    let mon_string_to_coef (Coef c, m) = (Coef (M.from_string_c c), m) in
    Sum (List.map mon_string_to_coef l)

  let from_string s = 
    string_to_coef (PolyParse.main PolyLexer.token (Lexing.from_string s))

  

(*  let division divisors f =
    let r = ref (sort_poly (Sum [])) in
    let mults = ref (List.map (fun _ -> sort_poly (Sum [])) divisors) in
    let s = List.length divisors in
    let p = ref f in
    while (not (is_zero !p)) do (
      let i = ref 1 in
      let division_occurred = ref false in
      while (!i <= s && not (!division_occurred)) do (
        let fi = List.nth divisors (!i - 1) in
        match M.divide_mon (lt !p) (lt fi) with
        | None -> i := !i + 1
        | Some new_mon -> (
          mults := List.mapi (fun j a -> if j= (!i-1) then add a (Sum [new_mon]) else a) !mults;
          p := add !p (mult minus_1 (mult (Sum [new_mon]) fi));
          division_occurred := true)
      )
      done;
      if not (!division_occurred) then (
        r := add !r (Sum [lt !p]);
        p := add !p (mult (Sum [(lt !p)]) minus_1))
    )
    done;
    (!mults, !r) *)
  
  let division_n divisors f =
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
    let rec aux p mults r = 
      if is_zero_n p then (mults, r)
      else 
        let ltp = lt p in
        let ltdiv fi = M.divide_mon ltp (lt fi) in
        match find_map ltdiv divisors with
        | None ->
          Log.log_line ~level:`trace "Division iteration. No divisor";
          Log.log_line ~level:`trace ("p := " ^ (to_string (unnormalize p)));
          let (N (Sum (plist))) = p in
          let p_rest = List.tl plist in
          let new_p = if List.length p_rest = 0 then (N zero) else N (Sum p_rest) in
          let new_r = add_n r (N (Sum [ltp])) in
          if List.length p_rest = 0 then
            aux new_p mults new_r
          else
            aux new_p mults new_r
        | Some (new_mon, i) ->
          Log.log_line ~level:`trace "Division iteration. Found divisor";
          let new_p = subtract_n p (mult_mon_poly new_mon (List.nth divisors i)) in
          Log.log_line ~level:`trace ((to_string (unnormalize new_p)) ^ ":= ("^ (to_string (unnormalize p)) ^ ") - " ^ "(" ^ (monomial_to_string new_mon) ^ ") * (" ^ (to_string (unnormalize (List.nth divisors i))) ^ ")");
          aux new_p (List.mapi (fun j x -> if j = i then add_n x (N (Sum [new_mon])) else x) mults) r
    in
    aux f (List.map (fun _ -> (N (Sum [(Coef (M.from_string_c "0"), Prod [])]))) divisors) (N (Sum [(Coef (M.from_string_c "0"), Prod [])]))

  let division divisors f =
    let (mults, r) = division_n (List.map normalize divisors) (normalize f) in
    (List.map unnormalize mults, unnormalize r)

  let s_poly f g =
    let lcmlm = M.lcm (lm f) (lm g) in
    let f_m = M.divide_mon (Coef (M.from_string_c "1"), lcmlm) (lt f) in
    let g_m = M.divide_mon (Coef (M.from_string_c "1"), lcmlm) (lt g) in
    match (f_m, g_m) with
    | (Some f_t, Some g_t) ->
      subtract_n (mult_mon_poly f_t f) (mult_mon_poly g_t g)
    | _ -> failwith "shouldn't happen"


  let minimize fs = 
    let monic_grobner = List.map 
      (fun poly -> 
        let lc = lc poly in
        mult_mon_poly (Coef (M.divc (M.from_string_c "1") lc), Prod []) poly
      ) fs in
    let is_need poly l = 
      let others = List.filter (fun p -> p <> poly) l in
      let divides x = match M.divide_mon (lt poly) (lt x) with | Some _ -> true | None -> false in
      not (List.exists divides others)
    in
    let rec filter candidates =
      match List.find_opt (fun x -> not (is_need x candidates)) candidates with
      | None -> candidates
      | Some poly -> filter (List.filter (fun x -> x <> poly) candidates)
    in
    filter monic_grobner

  let improved_buchberger (fs : M.coef polynomial list) = 
    let rec aux worklist g fss=
      Log.log_line ~level:`trace "Beginning Grobner iteration";
      let t = (List.length fss) - 1 in
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
              match M.divide_mon (lt (List.nth fss k)) lcmu with
              | None -> foo (k+1)
              | Some _ -> true
        in
        foo 0
      in
      match worklist with
      | [] -> g
      | (i, j) :: rest ->
        let (fi, fj) = (List.nth fss i, List.nth fss j) in
        let lcmlt = M.lcm (lm fi) (lm fj) in (* lt or lm? *)
        let prod = M.get_monic_mon (M.mult_mon (lt fi) (lt fj)) in
        if lcmlt = prod then aux rest g fss (* criterion *)
        else if criterion i j (Coef (M.from_string_c "1"), lcmlt) then aux rest g fss
        else (
          let s = snd (division_n g (s_poly fi fj)) in
          (*print_endline (to_string s);*)
          if is_zero_n s then aux rest g fss
          else 
            aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) fss)) (List.rev (List.sort compare_n (minimize (s :: g)))) (fss @ [s]) (*check this sorting *)
        )
    in
    let norm_fs = List.rev (List.sort compare_n (List.map normalize fs)) in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    let norm_g = aux (get_pairs (List.mapi (fun i _ -> i) norm_fs)) norm_fs norm_fs in
    List.map unnormalize norm_g



end

module Make ( C : Coefficient) = MakeP(MakeMon(C))


(*module Eliminate = struct

  let order = ref (let default = ref [] in let () = String.iter (fun c -> default := (Char.escaped c):: !default) "zyxwvutsrqponmlkjihgfedcba" in !default)

  let compare_var_s s1 s2 = 
    if (s1 = s2) then 0
    else if (List.find (fun v -> v = s1 || v = s2) !order) = s1 then (-1)
    else 1

  let compare_var (Exp (s1, e1)) (Exp (s2, e2)) = 
    if (s1 = s2) then compare e1 e2
    else compare_var_s s1 s2
  
  let multi_deg (Prod a) =
    let find_deg v = 
      match List.find_opt (fun (Exp (x, _)) -> x = v) a with
      | None -> 0
      | Some (Exp (_, c)) -> c
    in
    List.map find_deg !order

  let grevlex_ord a b = 
    let (adeg, bdeg) = (multi_deg a, multi_deg b) in
    let (tota, totb) = (List.fold_left (+) 0 adeg, List.fold_left (+) 0 bdeg) in
    if tota = totb then (
      try (-1) * (List.find ((<>) 0) (List.rev (List.map2 (-) adeg bdeg)))
      with Not_found -> 0)
    else compare tota totb
    
  let weight_order a b weight ord =
    let (adeg, bdeg) = (multi_deg a, multi_deg b) in
    let (ares, bres) = (List.fold_left2 (fun acc x y -> acc + (x * y)) 0 weight adeg, List.fold_left2 (fun acc x y -> acc + (x * y)) 0 weight bdeg) in
    if ares = bres then ord a b
    else compare ares bres
    
  let elimination_order vars_to_remove a b = 
    let weight = List.map (fun x -> if (List.exists ((=) x) vars_to_remove) then 1 else 0) !order in
    weight_order a b weight grevlex_ord

  let get_vars_m (_, Prod mon) = 
    List.map (fun (Exp (v, _)) -> v) mon

  let set_var_order polys vars =
    let get_vars (Sum poly) = List.concat (List.map get_vars_m poly) in
    let variables = List.concat (List.map get_vars polys) in
    let rec remove_dupes vs acc =
      match vs with
      | [] -> acc
      | v :: rest ->
        match (List.find_opt ((=) v) vars, List.find_opt ((=) v) acc)  with
        | (None, None) -> remove_dupes rest (v :: acc)
        | _ -> remove_dupes rest acc
    in
    order := (List.sort compare vars) @ (List.sort compare (remove_dupes variables []))

  let mon_cont_var v (_, Prod mon) = List.exists (fun (Exp (x, _)) -> x = v) mon

  let poly_cont_var v (Sum poly) = List.exists (mon_cont_var v) poly

  let eliminate polys remove =
    set_var_order polys remove;
    P.set_ord (elimination_order remove);
    let g = P.improved_buchberger polys in
    List.filter (fun poly -> not (List.exists (fun v -> poly_cont_var v poly) remove)) g

  let affine_hull polys = 
    set_var_order polys [];
    P.set_ord grevlex_ord;
    let g = P.improved_buchberger polys in
    List.filter P.is_lin g

end*)