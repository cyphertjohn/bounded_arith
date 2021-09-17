module type Polynomial =
  sig
  type mon

  type poly

  (** Get the monomials of a polynomial *)
  val get_mons : poly -> mon list

  (** Get the degree of a variable in a given monomial *)
  val get_degree : string -> mon -> int

  (** Get the vars of the monomial *)
  val get_vars_m : mon -> string list

  (**Computes the sum of two polynomials. *)
  val add :
    poly -> poly -> poly

  (** Multiplies two polynomials. *)
  val mul :
    poly -> poly -> poly
    
  (** Exponentiates a polynomial to some integer power.*)
  val exp_poly : poly -> int -> poly

  (** [substitute (x, p) q] substitutes [p] for every occurrence of [x] in [q].*)
  val substitute :
    string * poly -> poly -> poly

  (** Test if a polynomial is zero. *)
  val is_zero : poly -> bool

  (** Polynomial comparison. The result does not correspond to any arithmetic order.*)
  val compare : poly -> poly -> int
    
  (** Parses a string as a polynomial. *)
  val from_string : string -> poly

  (** Creates a polynomial out of a variable *)
  val from_var : string -> poly

  (** Creates a polynomial from a scalar constant given as a string*)
  val from_const_s : string -> poly

  (** Creates a polynomial from a variable and degree. *)
  val from_var_pow : string -> int -> poly

  (** Negates a polynomial *)
  val negate : poly -> poly

  (** Converts a polynomial to a string *)
  val to_string : poly -> string

  (** Gets the variables from a polynomial *)
  val get_vars : poly -> string list

  end

module Make (C : Sigs.Coefficient) = struct

  module PP = PrePoly.Make(C)

  module P = PolyParse.Make(PrePoly.Make(C))


  let from_string s = (P.main PolyLexer.token (Lexing.from_string s))


  include PP

  type mon = M.mon

end


module Ideal (C : Sigs.Coefficient) = struct

  include Make(C)

  type t = bool * poly list

  let initialize order : t = set_ord order; false, []

  let add_polys l (_, i) : t = (false, (List.map normalize l) @ i)

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
    let lcmlm = M.lcm_of_mon (lt f) (lt g) in
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

        let lcmlt = M.lcm_of_mon (lt fi) (lt fj) in (* lt or lm? *)
        let prod = (M.mult_mon (lt fi) (lt fj)) in
        if criterion i j lcmlt then aux rest g fss
        else if M.equal_monics lcmlt prod then aux rest g fss (* criterion *)
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
    let norm_fs = List.rev (List.sort compare fs) in
    let get_pairs l = List.filter (fun (x, y) -> x<>y) (fst(List.fold_left (fun (acc, l1) x -> (acc @ (List.map (fun y -> (x, y)) l1),List.tl l1)) ([],l) l)) in
    let norm_g = aux (get_pairs (List.mapi (fun i _ -> i) norm_fs)) norm_fs norm_fs in
    norm_g


  let reduce p ((calc_grob, basis) : t) : poly * t = 
    if calc_grob then (snd (division basis p)), (calc_grob, basis)
    else
      let grobner_basis = improved_buchberger basis in
      (snd (division grobner_basis p)), (true, grobner_basis)

end