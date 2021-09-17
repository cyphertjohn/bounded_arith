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

(** A functor for manipulating polynomials whose coeficients functions are given as input. *)
module Make :
  functor (C : Sigs.Coefficient) ->
  sig
    include Polynomial

    val from_const : C.coef -> poly

    val get_coef : mon -> C.coef
  end

module Ideal :
  functor (C : Sigs.Coefficient) -> 
  sig
    type t

    val add_polys : Make(C).poly list -> t -> t

    val initialize : (Make(C).mon -> Make(C).mon -> int) -> t

    val reduce : Make(C).poly -> t -> Make(C).poly * t

  end