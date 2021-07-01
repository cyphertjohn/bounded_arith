open Sigs.Expr
open Sigs.Polynomial
open Poly

module S = Map.Make(String)

let purify e =
  match e with
  | Coe x -> Coef x
  | Var x -> Exp (x, 1)

module Eliminate = struct

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
    Polynomial.set_ord (elimination_order remove);
    let g = Polynomial.improved_buchberger polys in
    List.filter (fun poly -> not (List.exists (fun v -> poly_cont_var v poly) remove)) g

  let affine_hull polys = 
    set_var_order polys [];
    Polynomial.set_ord grevlex_ord;
    let g = Polynomial.improved_buchberger polys in
    List.filter Polynomial.is_lin g

end