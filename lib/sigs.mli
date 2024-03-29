(**Module for keeping type signatures across the project. *)

(**Signature for field values. *)
module type Coefficient = sig 
  (** The type of constants *)
  type coef 

  (**Field addition. *)
  val addc : coef -> coef -> coef 

  (**Field multiplication. *)
  val mulc : coef -> coef -> coef

  (**Field division. *)
  val divc : coef -> coef -> coef 

  val exp : coef -> int -> coef

  (**Testing if equal to zero. *)
  val is_zero : coef -> bool

  (**Testing if equal to one. *)
  val is_one : coef -> bool
  
  (**Get the sign of a field value. *)
  val sgn : coef -> int

  (**Convert from a string. *)
  val from_string_c : string -> coef

  val of_int : int -> coef

  (**Convert to a string. *)
  val to_string_c : coef -> string

  (**Comparison *)
  val cmp : coef -> coef -> int

  (**Floor function. *)
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
    
  end

end

module V : Var

(**Q is an implementation of rational arithmetic using zarith. *)
module Q : Coefficient




(**Module for holding on to expression types. *)
module Expr : sig

  (**An expression is either
  - a constant
  - a variable
  - sum of expressions
  - product of expressions
  - division of two expressions
  - power of an expression and an integer
  - floor of an expression *)
  type 'a expr = 
  | Coe of 'a
  | Var of string
  | Add of 'a expr list
  | Mult of 'a expr list
  | Div of 'a expr * 'a expr
  | Pow of 'a expr * 'a expr 
  | Func of string * 'a expr
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

module Form : Formula

module FormT (C : Coefficient) : sig 

include Formula with type 'a form = 'a Form.form

val z3_to_expr_form : Z3.context -> Z3.Expr.expr -> (C.coef Expr.expr) form * string list
  
end