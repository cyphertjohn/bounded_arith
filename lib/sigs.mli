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

    (**Testing if equal to zero. *)
    val is_zero : coef -> bool

    (**Testing if equal to one. *)
    val is_one : coef -> bool
    
    (**Get the sign of a field value. *)
    val sgn : coef -> int

    (**Convert from a string. *)
    val from_string_c : string -> coef

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
end

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
    | Add of ('a expr) list
    | Mult of ('a expr) list
    | Div of ('a expr) * ('a expr)
    | Pow of ('a expr) * int 
    | Floor of ('a expr)
end