module type Coefficient = sig 
  type coef 
  val addc : coef -> coef -> coef 
  val mulc : coef -> coef -> coef
  val divc : coef -> coef -> coef
  val exp : coef -> int -> coef
  val is_zero : coef -> bool
  val is_one : coef -> bool
  val sgn : coef -> int
  val from_string_c : string -> coef
  val of_int : int -> coef
  val to_string_c : coef -> string
  val cmp : coef -> coef -> int
  val floor : coef -> coef
  val to_float : coef -> float
  val of_float : float -> coef
  val to_zarith : coef -> Q.t
  val of_zarith : Z.t -> coef
  val of_zarith_q : Q.t -> coef
  val one : coef
  val zero : coef
  val to_int : coef -> int option
end

module Q : Coefficient = struct 
  type coef = Q.t
  let addc = Q.add 
  let mulc = Q.mul
  let divc = Q.div
  let is_zero c = (Q.compare c (Q.of_string "0")) = 0
  let is_one c = (Q.compare c (Q.of_string "1")) = 0
  let sgn = Q.sign
  let to_string_c = Q.to_string
  let from_string_c = Q.of_string
  let of_int = Q.of_int
  let cmp = Q.compare
  let floor x = Q.of_bigint (Q.num x)
  let to_float = Q.to_float
  let of_float = Q.of_float
  let to_zarith (x : coef) : Q.t = x
  let of_zarith (x : Z.t) : coef = Q.make x Z.one
  let of_zarith_q (x : Q.t) : coef = x
  let exp c n = 
    let rec aux acc x e = 
      if e < 0 then aux acc (Q.inv x) (-e)
      else if e = 0 then acc
      else if e mod 2 = 0 then aux acc (Q.mul x x) (e/2)
      else aux (Q.mul acc x) (Q.mul x x) ((e-1)/2)
    in
    aux (Q.one) c n
  let one = Q.one
  let zero = Q.zero

  let to_int c = 
    if Z.compare Z.one (Q.den c) = 0 then
      Some (Z.to_int (Q.num c))
    else None
end

module type Var = sig
  type v
  
  val of_string : string -> v

  val fresh_var : unit -> v

  val to_string : v -> string

  val equal : v -> v -> bool

  val compare : v -> v -> int

  val hash : v -> int

  val of_int : int -> v

  val pp : Format.formatter -> v -> unit

  module S : sig
    type set
    val empty : set

    val add : v -> set -> set

    val union : set -> set -> set

    val mem : v -> set -> bool

    val diff : set -> set -> set

    val fold : (v  -> 'a -> 'a) -> set -> 'a -> 'a

    val to_list : set -> v list
  end

  module M : sig
    type +! 'a map

    include BatMap.S with type key = v and type +!'a t ='a map
    
    val domain : 'a map -> S.set
    
    (*val empty : 'a map

    val is_empty : 'a map -> bool

    val add : v -> 'a -> 'a map -> 'a map

    val find : v -> 'a map -> 'a

    val bindings : 'a map -> (t * 'a) list

    val fold : (t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b

    val mem : t -> 'a map -> bool

    val remove : t -> 'a map -> 'a map

    val modify_def : 'a -> t -> ('a -> 'a) -> 'a map -> 'a map

    val merge : (t -> 'a option -> 'b option -> 'c option) -> 'a map -> 'b map -> 'c map

    val domain : 'a map -> S.set*)
  end

  (*module Mi : sig
    type map
    val empty : map

    val is_empty : map -> bool

    val add : t -> int -> map -> map

    val find : t -> map -> int

    val fold : (t -> int -> 'b -> 'b) -> map -> 'b -> 'b

    val mem : t -> map -> bool

    val remove : t -> map -> map

    val modify_def : int -> t -> (int -> int) -> map -> map

    val domain : map -> S.set
  end*)
end

module V : Var = struct
let int_to_string = BatHashtbl.create 20
let string_to_int = BatHashtbl.create 20
let dummy_vars = ref BatISet.empty

let curr_num = ref 0
type v = int

let of_string (s : string) : v = 
  try BatHashtbl.find string_to_int s
  with Not_found ->
    BatHashtbl.add int_to_string !curr_num s;
    BatHashtbl.add string_to_int s !curr_num;
    curr_num := !curr_num + 1;
    !curr_num - 1
  
let to_string v = 
  if BatISet.mem v !dummy_vars then "x" ^ (string_of_int v)
  else 
    try BatHashtbl.find int_to_string v
    with Not_found -> failwith "Can't find " ^ (string_of_int v)

let fresh_var () = 
  dummy_vars := BatISet.add !curr_num !dummy_vars;
  curr_num := !curr_num + 1;
  !curr_num - 1

let equal = (=)

let compare = compare

let hash i = i

let of_int i = i

let pp f v =
  Format.pp_open_hbox f (); Format.pp_print_string f (to_string v); Format.pp_close_box f ()

module S = struct 
  type set = BatISet.t include BatISet 
  
  let to_list = BatISet.elements
  end

module M = struct 
  module B = BatMap.Make(struct type t = int let compare = compare end)
  type 'a map = 'a B.t
  include B
  let domain m = BatISet.of_enum (BatEnum.map (fun (a, _) -> (a, a)) (B.enum m))
end

(*module Mi = struct 
  type map = int BatIMap.t 
  include BatIMap 
  let empty = BatIMap.empty ~eq:(=)
  (*let bindings m = 
    let dset = BatIMap.domain m in
    BatISet.fold (fun v acc -> (v, BatIMap.find v m) :: acc) dset []*)
end*)

end


module Expr = struct
  type 'a expr = 
  | Coe of 'a
  | Var of string
  | Add of ('a expr) list
  | Mult of ('a expr) list
  | Div of ('a expr) * ('a expr)
  | Pow of ('a expr) * ('a expr) 
  | Func of string * ('a expr)
end

module type Formula = sig

type 'a form = 
  | Ge of 'a
  | Gt of 'a
  | Eq of 'a
  | Or of 'a form list
  | And of 'a form list

val map : ('a -> 'b) -> 'a form -> 'b form

val fold : ('a -> 'b -> 'a) -> 'a -> 'b form -> 'a

val get_atoms : 'a form -> 'a form list
  
end

module Form = struct


type 'a form = 
  | Ge of 'a
  | Gt of 'a
  | Eq of 'a
  | Or of 'a form list
  | And of 'a form list

let rec map f form = 
  match form with
  | Ge a -> Ge (f a)
  | Gt a -> Gt (f a)
  | Eq a -> Eq (f a)
  | Or list -> Or (List.map (map f) list)
  | And list -> And (List.map (map f) list)
  
let rec fold (f : 'a -> 'b -> 'a) (acc : 'a) (form : 'b form) =
  match form with
  | Ge (a : 'b) -> f acc a
  | Gt a -> f acc a
  | Eq a -> f acc a
  | Or list -> List.fold_left (fold f) acc list
  | And list -> List.fold_left (fold f) acc list

let rec get_atoms f =
  match f with
  | Ge a -> [Ge a]
  | Gt a -> [Gt a]
  | Eq a -> [Eq a]
  | Or list -> List.concat_map get_atoms list
  | And list -> List.concat_map get_atoms list

end

module FormT (C : Coefficient) = struct 
include Form

let nnf_rewriter ctx form = 
  let nnf_tactic = Z3.Tactic.mk_tactic ctx "nnf" in
  let g = Z3.Goal.mk_goal ctx false false false in
  Z3.Goal.add g [form];
  let ap_res = Z3.Tactic.ApplyResult.get_subgoals (Z3.Tactic.apply nnf_tactic g None) in
  Z3.Boolean.mk_and ctx (List.map Z3.Goal.as_expr ap_res)
  

let z3_to_expr_form ctx z3_form = 
  let quantified_vars_s = List.map (Z3.Symbol.to_string) (Z3.Quantifier.get_bound_variable_names (Z3.Quantifier.quantifier_of_expr z3_form)) in
  let quantified_vars_s = List.mapi (fun i v -> v ^ "!" ^ (string_of_int i)) (List.rev quantified_vars_s) in (*This is probably not a general solution*)
  Log.log_line_s ~level:`trace "Quantified vars";
  Log.log ~level:`trace (Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") Format.pp_print_string) (Some quantified_vars_s);
  let nnf_form = nnf_rewriter ctx z3_form in
  let atom_to_form negate z3_f = 
    Log.log_s ~level:`trace "Translating atom: ";
    Log.log_line_s ~level:`trace (Z3.Expr.to_string z3_f);
    let rec z3_expr_to_expr e =
      Log.log_s ~level:`trace "Translating term: ";
      Log.log_line_s ~level:`trace (Z3.Expr.to_string e);
      if Z3.Expr.is_const e then
        let name = Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e) in
        let v = Z3.Symbol.to_string name in
        if List.mem v quantified_vars_s || v = "__cost" then Expr.Var v, []
        else Expr.Var v, [v]
      else if Z3.Arithmetic.is_rat_numeral e then
        Expr.Coe (C.of_zarith_q (Z3.Arithmetic.Real.get_ratio e)), []
      else if Z3.Arithmetic.is_int_numeral e then
        Expr.Coe (C.from_string_c (Z3.Arithmetic.Integer.numeral_to_string e)), []
      else if Z3.Arithmetic.is_mul e then
        let lis, vs = List.fold_left (fun (lis, vars) f -> let (f_form, f_vars) = z3_expr_to_expr f in (f_form :: lis, f_vars @ vars)) ([], []) (Z3.Expr.get_args e) in
        Expr.Mult lis, vs
      else if Z3.Arithmetic.is_add e then
        let lis, vs = List.fold_left (fun (lis, vars) f -> let (f_form, f_vars) = z3_expr_to_expr f in (f_form :: lis, f_vars @ vars)) ([], []) (Z3.Expr.get_args e) in
        Expr.Add lis, vs
      else if Z3.Arithmetic.is_div e then
        let (num, num_vs), (den, den_vs) = z3_expr_to_expr (List.nth (Z3.Expr.get_args e) 0), z3_expr_to_expr(List.nth (Z3.Expr.get_args e) 1) in
        Expr.Div (num, den), num_vs @ den_vs
      else if Z3.Arithmetic.is_uminus e then
        let (neg_e, e_vs) = z3_expr_to_expr (List.hd (Z3.Expr.get_args e)) in
        Expr.Mult [Expr.Coe (C.from_string_c "-1"); neg_e], e_vs
      else if Z3.Arithmetic.is_real2int e || Z3.Arithmetic.is_int2real e then
        z3_expr_to_expr (List.hd (Z3.Expr.get_args e))
      else (*Other functions*)
        let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name (Z3.Expr.get_func_decl e)) in
        let args = Z3.Expr.get_args e in
        if name = "pow" then
          let base, base_vs = z3_expr_to_expr (List.nth args 0) in
          let exp, exp_vs = z3_expr_to_expr (List.nth args 1) in
          Expr.Pow (base, exp), base_vs @ exp_vs
        else if List.length args = 1 then
          let arg_e, arg_vs = z3_expr_to_expr (List.nth args 0) in
          Expr.Func (name, arg_e), arg_vs
        else
        failwith ("Not yet support for mutli-arity functions: " ^ (Z3.Expr.to_string e))
    in
    if Z3.Boolean.is_eq z3_f then
      let lhs, rhs = List.nth (Z3.Expr.get_args z3_f) 0, List.nth (Z3.Expr.get_args z3_f) 1 in
      let (lhs_e, lhs_vs), (rhs_e, rhs_vs) = z3_expr_to_expr lhs, z3_expr_to_expr rhs in
      let lhs_minus_rhs = Expr.Add [lhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); rhs_e]] in
      if (not negate) then [Eq lhs_minus_rhs], lhs_vs @ rhs_vs
      else [Gt lhs_minus_rhs; Gt (Expr.Add [rhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); lhs_e]])], lhs_vs @ rhs_vs
    else if Z3.Arithmetic.is_ge z3_f then
      let lhs, rhs = List.nth (Z3.Expr.get_args z3_f) 0, List.nth (Z3.Expr.get_args z3_f) 1 in
      let (lhs_e, lhs_vs), (rhs_e, rhs_vs) = z3_expr_to_expr lhs, z3_expr_to_expr rhs in
      if not negate then [Ge (Expr.Add [lhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); rhs_e]])], lhs_vs @ rhs_vs
      else [Gt (Expr.Add [rhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); lhs_e]])], lhs_vs @ rhs_vs
    else if Z3.Arithmetic.is_gt z3_f then
      let lhs, rhs = List.nth (Z3.Expr.get_args z3_f) 0, List.nth (Z3.Expr.get_args z3_f) 1 in
      let (lhs_e, lhs_vs), (rhs_e, rhs_vs) = z3_expr_to_expr lhs, z3_expr_to_expr rhs in
      if not negate then [Gt (Expr.Add [lhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); rhs_e]])], lhs_vs @ rhs_vs
      else [Ge (Expr.Add [rhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); lhs_e]])], lhs_vs @ rhs_vs
    else if Z3.Arithmetic.is_le z3_f then
      let lhs, rhs = List.nth (Z3.Expr.get_args z3_f) 0, List.nth (Z3.Expr.get_args z3_f) 1 in
      let (lhs_e, lhs_vs), (rhs_e, rhs_vs) = z3_expr_to_expr lhs, z3_expr_to_expr rhs in
      if not negate then [Ge (Expr.Add [rhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); lhs_e]])], lhs_vs @ rhs_vs
      else [Gt (Expr.Add [lhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); rhs_e]])], lhs_vs @ rhs_vs
    else if Z3.Arithmetic.is_lt z3_f then
      let lhs, rhs = List.nth (Z3.Expr.get_args z3_f) 0, List.nth (Z3.Expr.get_args z3_f) 1 in
      let (lhs_e, lhs_vs), (rhs_e, rhs_vs) = z3_expr_to_expr lhs, z3_expr_to_expr rhs in
      if not negate then [Gt (Expr.Add [rhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); lhs_e]])], lhs_vs @ rhs_vs
      else [Ge (Expr.Add [lhs_e; Expr.Mult [Expr.Coe (C.from_string_c "-1"); rhs_e]])], lhs_vs @ rhs_vs
    else failwith ("Unknown z3 atom: " ^ (Z3.Expr.to_string z3_f))
  in        
  let rec aux z3_f = 
    if Z3.Boolean.is_or z3_f then
      let lis, vs = List.fold_left (fun (lis, vars) f -> let (f_form, f_vars) = aux f in (f_form :: lis, f_vars @ vars)) ([], []) (Z3.Expr.get_args z3_f) in
      Or lis, vs
    else if Z3.Boolean.is_and z3_f then
      let lis, vs = List.fold_left (fun (lis, vars) f -> let (f_form, f_vars) = aux f in (f_form :: lis, f_vars @ vars)) ([], []) (Z3.Expr.get_args z3_f) in
      And lis, vs
    else if Z3.Boolean.is_not z3_f then
      let atoms, atom_vs = atom_to_form true (List.hd (Z3.Expr.get_args z3_f)) in
      if List.length atoms = 1 then List.hd atoms, atom_vs
      else And atoms, atom_vs
    else
      let atoms, atom_vs = atom_to_form false z3_f in
      if List.length atoms = 1 then List.hd atoms, atom_vs
      else And atoms, atom_vs
  in
  let form, vars_to_keep = aux nnf_form in
  let rec remove_dups lst= match lst with
    | [] -> []
    | h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t)) in
  form, remove_dups vars_to_keep

end