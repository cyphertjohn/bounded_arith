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
end

module type Var = sig
    type t
    
    val of_string : string -> t

    val fresh_var : unit -> t

    val to_string : t -> string

    val equal : t -> t -> bool

    val compare : t -> t -> int

    val hash : t -> int

    module S : sig
      type set
      val empty : set

      val add : t -> set -> set

      val union : set -> set -> set

      val mem : t -> set -> bool

      val diff : set -> set -> set

      val fold : (t  -> 'a -> 'a) -> set -> 'a -> 'a
    end

    module M : sig
      type 'a map
      val empty : 'a map

      val is_empty : 'a map -> bool

      val add : t -> 'a -> 'a map -> 'a map

      val find : t -> 'a map -> 'a

      val bindings : 'a map -> (t * 'a) list

      val fold : (t -> 'a -> 'b -> 'b) -> 'a map -> 'b -> 'b

      val mem : t -> 'a map -> bool

      val remove : t -> 'a map -> 'a map

      val modify_def : 'a -> t -> ('a -> 'a) -> 'a map -> 'a map

      val merge : (t -> 'a option -> 'b option -> 'c option) -> 'a map -> 'b map -> 'c map

      val domain : 'a map -> S.set
    end

    module Mi : sig
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
    | Add of ('a expr) list
    | Mult of ('a expr) list
    | Div of ('a expr) * ('a expr)
    | Pow of ('a expr) * int 
    | Floor of ('a expr)
end