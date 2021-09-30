(** A functor for manipulating polynomials whose coeficients functions are given as input. *)
module Make :
  functor (C : Sigs.Coefficient) ->
  sig
  type monic_mon

  type mon = C.coef * monic_mon

  type poly

  (** Get the monomials of a polynomial *)
  val get_mons : poly -> mon list

  (** Get the degree of a variable in a given monomial *)
  val get_degree : string -> monic_mon -> int

  (** Get the vars of the monomial *)
  val get_vars_m : monic_mon -> string list

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

  val from_const : C.coef -> poly

  end

module Ideal :
  functor (C : Sigs.Coefficient) -> 
  sig
    type ideal

    val add_polys : Make(C).poly list -> ideal -> ideal

    val initialize : (Make(C).monic_mon -> Make(C).monic_mon -> int) -> ideal

    val reduce : Make(C).poly -> ideal -> Make(C).poly * ideal

  end

module Cone :
  functor (C : Sigs.Coefficient) -> 
  sig
    type cone

    val add_eqs : Make(C).poly list -> cone -> cone

    val add_ineqs : Make(C).poly list -> cone -> cone

    val initialize : (Make(C).monic_mon -> Make(C).monic_mon -> int) -> cone

    val reduce : Make(C).poly -> cone -> Make(C).poly * cone

  end