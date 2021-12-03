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
    let rec aux p mults (r : sorted_poly) = 
      (*Log.log_s ~level:`trace "Division iteration\nDivisor: ";
      Log.log ~level:`trace pp (fst p);
      Log.log_s ~level:`trace "Current Remainder: ";
      Log.log ~level:`trace pp (fst r);*)
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
          subtract (fst p) (mult_mon_poly new_mon (fst (List.nth divisors i)));
          List.iteri (fun j x -> if j = i then add_mon x new_mon) mults;
          aux (make_sorted_poly ord (fst p)) mults r
    in
    aux f (List.map (fun _ -> (make_poly_from_mon Mon.zero)) divisors) ((make_poly_from_mon Mon.zero), [])

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
    filter [] monic_grobner

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
      | [] -> {basis = I (minimize g); ord}
      | (i, j) :: rest ->
        let (fi, fj) = (List.nth g i, List.nth g j) in
        let lcmlt = Mon.lcm_of_mon (snd (lt fi)) (snd (lt fj)) in (* lt or lm? *)
        let prod = (Mon.mult_mon (lt fi) (lt fj)) in
        if criterion i j (Mon.from_string_c "1", lcmlt) then aux rest g
        else if Mon.lex_ord lcmlt (snd prod) = 0 then aux rest g (* criterion *)
        else (
          let sp = s_poly ord fi fj in
          let (_, s) = division ord g sp in
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
    Format.pp_print_string f "Ideal";
    Format.print_newline ();
    let str =
      match i.basis with
      | Top -> "<1>"
      | Bot -> "<0>"
      | I basis -> "<" ^ (String.concat ", " (List.map (fun (p,_) -> to_string p) basis)) ^ ">"
    in
    Format.pp_print_string f str;
    Format.print_newline ()

  let reduce p (i : ideal) : poly = 
    match i.basis with
    | Top -> from_const_s "0"
    | Bot -> p
    | I basis -> fst (snd (division i.ord basis (make_sorted_poly i.ord p)))

  let make_ideal ord eqs : ideal = 
    let normal = List.filter (fun p -> not (is_zero p)) eqs in
    if List.length normal = 0 || List.for_all is_zero normal then 
      {basis = Bot; ord}
    else if List.exists is_const normal then 
      {basis = Top; ord}
    else 
      let res = improved_buchberger ord normal in
      res
  
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

    type monic_mon

    type impl = poly * poly

    val (=>) : poly -> poly -> impl

    val make_cone : ?sat:int -> ?ord:(monic_mon -> monic_mon -> int) -> ?eqs:poly list -> ?ineqs:poly list -> ?impls: impl list -> unit -> cone

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
      ineqs : poly list list
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
      let reduced_ineqs = List.map (fun i -> I.reduce i c.ideal) ins in
      List.filter (fun p -> not (is_not_neg_const p)) reduced_ineqs
    in
    let ine_red = I.reduce ine c.ideal in
    if is_not_neg_const ine_red then c
    else if List.length c.ineqs = 0 then 
      let rec aux acc depth = 
        if depth <= 0 then acc
        else 
          aux ([I.exp_poly ine_red depth] :: acc) (depth - 1)
      in
      {depth = c.depth; ideal = c.ideal; ineqs= (List.map minimize_ineqs (aux [] c.depth))}
    else 
      let folder acc curr_level = 
        if List.length acc = 0 then [ine_red :: curr_level]
        else
          let prev_level = List.hd acc in
          ((List.map (fun p -> I.mul ine_red p) prev_level) @ curr_level) :: acc
      in
      let new_ineqs = List.map minimize_ineqs (List.rev (List.fold_left folder [] c.ineqs)) in
      {depth = c.depth;ideal = c.ideal; ineqs= new_ineqs}


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
    
  let pp_prob f prob = 
    let prob_str = Lp.Problem.to_string ~short:true prob in
    Format.pp_print_string f prob_str;
    Format.print_newline ()


  let is_non_neg p c = 
    let id, ineqs = c.ideal, c.ineqs in
    let p_ired = I.reduce p id in
    if is_not_neg_const p_ired then true
    else
      let ineqs = List.concat ineqs in
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
    Log.log ~level:`trace pp_prob prob;
    match Lp_glpk.solve ~term_output:false prob with
    | Ok _ -> true
    | Error _ -> false

  let reduce_ineq ord p ineqs = 
    Log.log_line_s ~level:`trace "Trying to reduce by ineqs";
    if List.length ineqs = 0 then p
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
        let prob = Lp.Problem.make (Lp.Objective.minimize Lp.Poly.zero) (hard_cnsts @ rs) in
        Log.log ~level:`trace pp_prob prob;
        match Lp_glpk.solve ~term_output:false prob with
        | Ok (_, s) ->
          let folder r_s r_val res = 
            try
              let r_val_c = Mon.of_float r_val in
              if Mon.cmp r_val_c (Mon.from_string_c "0") = 0 then res
              else 
                let r_dim = S.find r_s r_to_dim in
                let r_mon = DimMap.find r_dim dim_map in
                (r_val_c, r_mon) :: res
            with Not_found -> res
          in
          Lp.PMap.fold folder s []
        | Error _ -> find_optimal_sol (List.tl rs)
      in
      Log.log_line_s ~level:`trace "trying to find optimal solution";
      from_mon_list (find_optimal_sol r_cnsts)
        
  let reduce_eq p c = I.reduce p c.ideal

  let reduce p c = 
    let p_ired = I.reduce p c.ideal in
    let p_ineq_red = reduce_ineq c.ideal.ord p_ired (List.concat c.ineqs) in
    p_ineq_red
    

  let get_eq_basis c = I.get_generators c.ideal

  let get_ineq_basis c = 
    if List.length c.ineqs = 0 then [I.from_const_s "0"]
    else
      List.hd c.ineqs

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
    let prod_sat_cone = List.fold_left add_ineq {depth=sat; ideal= ideal; ineqs= []} ineqs in
    saturate prod_sat_cone impls

  let ppc f c = 
      Format.pp_print_string f "Cone";
      Format.print_newline ();
      ppi f c.ideal;
      let str =
        if List.length c.ineqs = 0 then "Ineqs: [0]"
        else
          "Basis Ineqs: [" ^ (String.concat ", " (List.map to_string (List.hd c.ineqs))) ^ "]\n" (*^ 
          "Derived Ineqs: [" ^ (String.concat ", " (List.map to_string (List.concat (List.tl c.ineqs)))) ^ "]"*) in
      Format.pp_print_string f str;
      Format.print_newline ()

end

module ConeQ = Cone(Sigs.Q)

module IdealQ = Ideal(Sigs.Q)