module type Polynomial = sig
  type monic_mon

  type coef

  type mon = coef * monic_mon

  type poly

  val get_mons : poly -> mon list

  val get_degree : string -> monic_mon -> int

  val get_vars_m : monic_mon -> string list

  val add :
    poly -> poly -> poly

  val mul :
    poly -> poly -> poly
    
  val exp_poly : poly -> int -> poly

  val substitute :
    string * poly -> poly -> poly

  val is_zero : poly -> bool

  val compare : poly -> poly -> int
    
  val from_string : string -> poly

  val from_var : string -> poly

  val from_const_s : string -> poly

  val from_var_pow : string -> int -> poly

  val negate : poly -> poly

  val to_string : poly -> string

  val get_vars : poly -> string list

  val from_const : coef -> poly
end

module Make (C : Sigs.Coefficient) = struct

  module PP = PrePoly.Make(C)

  module P = PolyParse.Make(PrePoly.Make(C))


  let from_string s = (P.main PolyLexer.token (Lexing.from_string s))


  include PP

  type monic_mon = M.monic_mon

  type mon = C.coef * monic_mon

  type coef = C.coef

end

module PQ = Make(Sigs.Q)

module Ideal (C : Sigs.Coefficient) = struct

  include Make(C)

  type ideal = poly list


  let division divisors f =
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
      if is_zero p then (mults, r)
      else 
        let ltp = lt p in
        let ltdiv fi = M.divide_mon ltp (lt fi) in
        match find_map ltdiv divisors with
        | None ->
          let (NSum (plist)) = p in
          let p_rest = List.tl plist in
          let new_p = if List.length p_rest = 0 then (NSum [M.zero]) else NSum p_rest in
          let new_r = add r (NSum [ltp]) in
          aux new_p mults new_r
        | Some (new_mon, i) ->
          let new_p = subtract p (mult_mon_poly new_mon (List.nth divisors i)) in
          aux new_p (List.mapi (fun j x -> if j = i then add x (NSum [new_mon]) else x) mults) r
    in
    aux f (List.map (fun _ -> (NSum [M.zero])) divisors) (NSum [M.zero])

  let s_poly f g =
    let lcmlm = (M.from_string_c "1", M.lcm_of_mon (snd (lt f)) (snd (lt g))) in
    let f_m = M.divide_mon lcmlm (lt f) in
    let g_m = M.divide_mon lcmlm (lt g) in
    match (f_m, g_m) with
    | (Some f_t, Some g_t) ->
      subtract (mult_mon_poly f_t f) (mult_mon_poly g_t g)
    | _ -> failwith "shouldn't happen"


  let minimize fs = 
    let monic_grobner = List.map 
      (fun poly -> 
        let lc = lc poly in
        let lc_recip = M.divc (M.from_string_c "1") lc in
        mult_mon_poly (M.make_mon_from_coef lc_recip) poly
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

  let improved_buchberger fs = 
    let rec aux worklist g fss=
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
      | [] -> minimize g
      | (i, j) :: rest ->
        let (fi, fj) = (List.nth fss i, List.nth fss j) in
        (*Log.log_line ~level:`trace "Beginning Grobner iteration";
        Log.log_line ~level:`trace "Current g:\n";
        List.iter (fun x -> Log.log_line ~level:`trace (to_string_n x)) g;*)

        let lcmlt = M.lcm_of_mon (snd (lt fi)) (snd (lt fj)) in (* lt or lm? *)
        let prod = (M.mult_mon (lt fi) (lt fj)) in
        if criterion i j (M.from_string_c "1", lcmlt) then aux rest g fss
        else if !M.ord lcmlt (snd prod) = 0 then aux rest g fss (* criterion *)
        else (
          (*Log.log_line ~level:`trace ("Found potential s_poly:");
          Log.log_line ~level:`trace ("\nfi: " ^ (to_string_n fi));
          Log.log_line ~level:`trace ("fj: " ^ (to_string_n fj) ^ "\n");*)
          let sp = s_poly fi fj in
          let (_, s) = division g sp in
          (*Log.log_line ~level:`trace ("s_poly = " ^ (to_string_n sp));
          let (_, s) = Log.log_time_cum "Division" (division_n g) sp in
          Log.log_line ~level:`trace ("After reduction: " ^ (to_string_n s));*)
          (*print_endline (to_string s);*)
          if is_zero s then aux rest g fss
          else 
            aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) fss)) (s :: g) (fss @ [s])
            (*aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) fss)) (minimize (s :: g)) (fss @ [s])*)
            (*aux (worklist @ (List.mapi (fun i _ -> (i, t+1)) fss)) (List.rev (List.sort compare_n (minimize (s :: g)))) (fss @ [s])*) (*check this sorting *)
        )
    in
    let norm_fs = List.rev (List.sort compare (List.filter (fun p -> not (is_zero p)) fs)) in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    let norm_g = aux (get_pairs (List.mapi (fun i _ -> i) norm_fs)) norm_fs norm_fs in
    norm_g



  let reduce p (basis : ideal) : poly = 
    if List.length basis = 0 then (normalize p)
    else (snd (division basis (normalize p)))


  let ppi f (basis : ideal) = 
    Format.pp_print_string f ("Grobner Basis: <" ^ (String.concat ", " (List.map to_string basis)) ^ ">")

  let make_ideal order eqs : ideal = 
    set_ord order; 
    improved_buchberger (List.map normalize eqs)

  let get_generators (basis : ideal) : poly list = basis

end

module type Cone = sig 
    type cone

    type poly

    type monic_mon

    val make_cone : ?sat:int -> (monic_mon -> monic_mon -> int) -> poly list -> poly list -> cone

    val reduce : poly -> cone -> poly

    val reduce_eq : poly -> cone -> poly

    val get_eq_basis : cone -> poly list

    val get_ineq_basis : cone -> poly list
end


module Cone(C : Sigs.Coefficient) = struct
  module I = Ideal(C)
  include I
  
  type cone = int * I.ideal * poly list * poly list

  let make_cone ?(sat = 1) order eqs ineqs : cone = 
    let ideal = make_ideal order eqs in
    let minimize_ineqs ins = 
      let reduced_ineqs = List.map (fun i -> I.reduce i ideal) ins in
      let is_not_const p = 
        if I.is_const p then
          let c = fst (List.hd (I.get_mons p)) in
          if I.M.cmp c (I.M.from_string_c "0") < 0 then failwith "inconsistent cone"
          else false
        else true
      in
      let no_const = List.filter is_not_const reduced_ineqs in
      let sorted_ineqs  = List.sort I.compare no_const in
      let folder (acc, prev) curr = 
        if I.compare prev curr = 0 then (acc, prev)
        else (prev :: acc, curr)
      in
      if List.length sorted_ineqs = 0 then []
      else  
        let (acc, last) = List.fold_left folder ([], List.hd sorted_ineqs) (List.tl sorted_ineqs) in
        List.rev (last :: acc)
    in
    let saturate ine depth =
      let increase_level level = 
        fst (List.fold_left 
          (fun (a, r) p -> 
            a @ (List.map (fun x -> mul p x) r), List.tl r
          )
          ([], level) ine)
      in
      let rec aux (acc, prev_level) level = 
        if level <= 1 then acc @ prev_level
        else 
          aux (acc @ prev_level, increase_level prev_level) (level - 1)
      in
      if depth <= 1 then []
      else
        let second_level = increase_level ine in
        aux ([], second_level) (depth - 1)
    in
    let min_ineqs = minimize_ineqs (List.map normalize ineqs) in
    let derived_ineqs = minimize_ineqs (saturate min_ineqs sat) in
    (sat, ideal, min_ineqs, derived_ineqs)


  module MonMap = BatMap.Make(struct type t = monic_mon let compare a b = mon_order (M.from_string_c "1", a) (M.from_string_c "1", b) end)

  module DimMap = BatIMap

  module MonSet = BatSet.Make(struct type t = monic_mon let compare a b = mon_order (M.from_string_c "1", a) (M.from_string_c "1", b) end)

  module S = BatMap.Make(struct type t = Lp.Poly.t let compare = Lp.Poly.compare end)

  let polys_to_dim polys = 
    let add_mons curr_set poly = 
      List.fold_left (fun s m -> MonSet.add m s) curr_set (List.map snd (get_mons poly))
    in
    let mon_set = List.fold_left add_mons MonSet.empty polys in
    let curr_dim = ref 0 in
    let rec generate_dims curr_set curr_dim_map curr_mon_map = 
      try 
        let mon, new_set = MonSet.pop_max curr_set in
        let new_dim_map = DimMap.add !curr_dim mon curr_dim_map in
        let new_mon_map = MonMap.add mon !curr_dim curr_mon_map in
        curr_dim := !curr_dim + 1;
        generate_dims new_set new_dim_map new_mon_map
      with Not_found -> curr_dim_map, curr_mon_map
    in
    let dim_map, mon_map = generate_dims mon_set (DimMap.empty ~eq:(fun x y -> !M.ord x y = 0)) (MonMap.empty) in
    let poly_to_coef_map poly = 
      List.fold_left (fun acc (c, mon) -> 
        let dim = MonMap.find mon mon_map in
        DimMap.add dim c acc) (DimMap.empty ~eq:(fun x y -> M.cmp x y = 0)) (get_mons poly)
    in
    dim_map, List.map poly_to_coef_map polys
    
      
  let reduce_ineq p ineqs = 
    if List.length ineqs = 0 then p
    else 
      let neg_ineqs = ineqs (*List.map negate ineqs*) in
      let dim_map, p_ineq = polys_to_dim (p :: neg_ineqs) in
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
            Lp.Poly.(++) sum (Lp.Poly.expand (Lp.Poly.c (M.to_float dim_c)) lambda)
          with Not_found -> sum
          in
        let sum = List.fold_left generate_lhs_sum (Lp.Poly.zero) ineq_dim_lambda in
        let r = Lp.Poly.var ~lb:Float.neg_infinity ("r" ^ (string_of_int dim)) in
        let p_coef = 
          try Lp.Poly.c (M.to_float (DimMap.find dim p_dim))
          with Not_found -> Lp.Poly.zero
        in
        let new_cnst = Lp.Cnstr.eq (Lp.Poly.(++) sum r) p_coef in
        let r_zero = Lp.Cnstr.eq r Lp.Poly.zero in
        new_cnst :: hard_cnsts, r_zero :: r_cnsts, S.add r dim r_map
      in
      let hard_cnsts, r_cnsts, r_to_dim = DimMap.fold generate_cnstrs dim_map ([], [], S.empty) in
      let rec find_optimal_sol rs = 
        let prob = Lp.Problem.make (Lp.Objective.minimize Lp.Poly.zero) (hard_cnsts @ rs) in
        Log.log_line ~level:`trace (Lp.Problem.to_string ~short:true prob);
        match Lp_glpk.solve ~term_output:false prob with
        | Ok (_, s) ->
          let folder r_s r_val res = 
            try
              let r_val_c = M.of_float r_val in
              if M.cmp r_val_c (M.from_string_c "0") = 0 then res
              else 
                let r_dim = S.find r_s r_to_dim in
                let r_mon = DimMap.find r_dim dim_map in
                (r_val_c, r_mon) :: res
            with Not_found -> res
          in
          Lp.PMap.fold folder s []
        | Error _ -> find_optimal_sol (List.tl rs)
      in
      from_mons (find_optimal_sol r_cnsts)
        
  let reduce_eq p ((_, id, _, _) : cone) = I.reduce p id

  let reduce p ((_, ide, ineqs, derived_ineqs) : cone) = 
    let p_ired = I.reduce p ide in
    let p_ineq_red = reduce_ineq p_ired (ineqs @ derived_ineqs) in
    p_ineq_red
    

  let get_eq_basis ((_, ide, _, _) : cone) = I.get_generators ide

  let get_ineq_basis ((_, _, ineqs, _) : cone) = ineqs

end

module ConeQ = 
  struct
    include Cone(Sigs.Q)
    
    let ppc f ((_, i, ineqs, derived_ineqs) : cone) = 
    ppi f i;
    let str = "Basis Ineqs: [" ^ (String.concat ", " (List.map to_string ineqs)) ^ "]" in
    let str = str ^ "\nDerived Ineqs: [" ^ (String.concat ", " (List.map to_string derived_ineqs)) ^ "]" in
    Format.pp_print_string f str

  end