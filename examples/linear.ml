module CC = Bound.Poly.Cone(Bound.Sigs.Q)

module P = Bound.Poly.Make(Bound.Sigs.Q)

let t = P.from_string "x^2 + y + z^2 + 3";;

let iq1 = P.from_string "x^2 - 1";;

let iq2 = P.from_string "y + 1";;

let lex_ord a b = 
  let av, bv = List.sort compare (P.get_vars_m a), List.sort compare (P.get_vars_m b) in
  let rec ord avl bvl = 
    match avl, bvl with
    | [], [] -> 0
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | x :: xs, y :: ys ->
      if compare x y = 0 then
        let xd, yd = P.get_degree x a, P.get_degree y b in
        if compare xd yd = 0 then ord xs ys
        else compare xd yd
      else compare y x
  in
  ord av bv
  

let c = CC.add_ineqs ([iq1;iq2]) (CC.initialize lex_ord);;

let res, _ = CC.reduce t c;;

print_endline (P.to_string res);;