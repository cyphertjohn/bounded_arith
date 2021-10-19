module type Polynomial = sig
  type monic_mon

  type coef

  type mon = coef * monic_mon

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

  (** Initialize a polynomial from a constant *)
  val from_const : coef -> poly
end

(** A functor for manipulating polynomials whose coeficients functions are given as input. *)
module Make :
  functor (C : Sigs.Coefficient) -> Polynomial with type coef = C.coef


module PQ : 
  sig 
    include (Polynomial with type coef = Sigs.Q.coef)

    val pp : Format.formatter -> poly -> unit [@@ocaml.toplevel_printer]

    val ppm : Format.formatter -> mon -> unit [@@ocaml.toplevel_printer]

    val ppmm : Format.formatter -> monic_mon -> unit [@@ocaml.toplevel_printer]
  end

(** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
module Ideal :
  functor (C : Sigs.Coefficient) -> 
  sig

    (** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
    type ideal

    (** Initialize an ideal with a given monomial order and set of generators.*)
    val make_ideal : (Make(C).monic_mon -> Make(C).monic_mon -> int) -> Make(C).poly list -> ideal

    (** Reduce a polynomial by an ideal. That is [reduce p i], returns r, such that p = f + r, 
    with r minimum in the monomial order with f in the ideal.*)
    val reduce : Make(C).poly -> ideal -> Make(C).poly

    (** Get the generators (Grobner basis) of an ideal. *)
    val get_generators : ideal -> Make(C).poly list

  end

module type Cone = sig 
  (** A (linear) cone consists of an ideal, representing equations, and all positive linear combinations of a set of inequalities.
    Thus, each polynomial in the cone represents a positive polynomial. *)
    type cone

    type poly

    type monic_mon

    (** [make_cone sat ord eq ineqs] creates a linear cone from a given monomial order [ord], a list of equations [eq], and a list of ineqs [ineqs] (assumed to be nonnegative). 
    The optional [sat] parameter will mutliply inequalities together up to the [sat] limit. Default is 1.*)
    val make_cone : ?sat:int -> (monic_mon -> monic_mon -> int) -> poly list -> poly list -> cone

    (** Reduce a polynomial by a cone. That is [reduce p i], returns r, such that p = -f + r, 
    with the leading term of r minimum in the monomial order and f in the cone. Since f is a member of the cone it is nonnegative, so p <= r.*)
    val reduce : poly -> cone -> poly

    (** Reduce a polynomial by a cone only using the equations of the cone. *)
    val reduce_eq : poly -> cone -> poly

    (**Get the basis polynomials for the ideal part of the cone. *)
    val get_eq_basis : cone -> poly list

    (** Get the inequalities of the cone. *)
    val get_ineq_basis : cone -> poly list
end


(** A (linear) cone consists of an ideal, representing equations, and all positive linear combinations of a set of inequalities.
    Thus, each polynomial in the cone represents a positive polynomial. *)
module Cone :
  functor (C : Sigs.Coefficient) -> Cone

module ConeQ : sig

  include (Cone with type poly := PQ.poly and type monic_mon := PQ.monic_mon )

  val ppc : Format.formatter -> cone -> unit [@@ocaml.toplevel_printer]

end