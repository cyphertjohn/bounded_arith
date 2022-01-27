module type Polynomial = sig
  type monic_mon

  type coef

  type mon = coef * monic_mon

  type poly

  (** Get the monomials of a polynomial *)
  val get_mons : poly -> mon BatEnum.t

  (** Get the degree of a variable in a given monomial *)
  val get_degree : string -> monic_mon -> int

  (** Get the vars of the monomial *)
  val get_vars_m : monic_mon -> string BatEnum.t

  (**Computes the sum of two polynomials. *)
  val add :
    poly -> poly -> poly

  (**Computes the sum of two polynomials, and store the result in the first argument. *)
  val addi :
    poly -> poly -> unit

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

  (** Test if a polynomial is constant. *)
  val is_const : poly -> bool

  (** Polynomial comparison. The result does not correspond to any arithmetic order.*)
  val compare : poly -> poly -> int

  (** Cheaper equality testing than compare. *)
  val equal : poly -> poly -> bool
    
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
  val get_vars : poly -> string BatEnum.t

  (** Initialize a polynomial from a constant *)
  val from_const : coef -> poly

  (*(** Normalizes a polynomial. Only used when passing polynomials between modules, where one module might use a different order. *)
  val normalize : poly -> poly*)
end

(** A functor for manipulating polynomials whose coeficients functions are given as input. *)
module Make :
  functor (C : Sigs.Coefficient) -> Polynomial with type coef = C.coef


module PQ : 
  sig 
    include (Polynomial with type coef = Sigs.Q.coef)

    val pp : ?ord:(monic_mon -> monic_mon -> int) -> Format.formatter -> poly -> unit [@@ocaml.toplevel_printer]

    val ppm : Format.formatter -> mon -> unit [@@ocaml.toplevel_printer]

    val ppmm : Format.formatter -> monic_mon -> unit [@@ocaml.toplevel_printer]
  end

module type Ideal = sig 
 (** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
    type ideal

    type poly

    type monic_mon

    (** Initialize an ideal with a given monomial order and set of generators.*)
    val make_ideal : (monic_mon -> monic_mon -> int) -> poly list -> ideal

    val make_ideal_f : int BatMap.String.t -> bool BatMap.String.t -> (int * string) list -> poly list -> ideal

    (** Test whether a polynomial is a member of the ideal. *)
    val mem : poly -> ideal -> bool

    (** Reduce a polynomial by an ideal. That is [reduce p i], returns r, such that p = f + r, 
    with r minimum in the monomial order with f in the ideal.*)
    val reduce : poly -> ideal -> poly

    (** Get the generators (Grobner basis) of an ideal. *)
    val get_generators : ideal -> poly list

    val ppi : Format.formatter -> ideal -> unit

    val equal : ideal -> ideal -> bool

end

(** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
module Ideal :
  functor (C : Sigs.Coefficient) -> Ideal


module IdealQ : sig
  include (Ideal with type poly := PQ.poly and type monic_mon := PQ.monic_mon)

  val ppi : Format.formatter -> ideal -> unit [@@ocaml.toplevel_printer]

end

module type Cone = sig 
  (** A (linear) cone consists of an ideal, representing equations, and all positive linear combinations of a set of inequalities.
    Thus, each polynomial in the cone represents a positive polynomial. *)
    type cone

    type ideal

    type poly

    type monic_mon

    (**An implication is a pair of polynomials. The head of the implication is the first element, and the consequent is the second element. *)
    type impl = poly * poly

    (**Infix operator for creating an implication. *)
    val (=>) : poly -> poly -> impl

    (** [make_cone sat ord eq ineqs] creates a linear cone from a given monomial order [ord], a list of equations [eq], and a list of ineqs [ineqs] (assumed to be nonnegative). 
    The optional [sat] parameter will mutliply inequalities together up to the [sat] limit. Default is 1.*)
    val make_cone : ?sat:int -> ?ord:(monic_mon -> monic_mon -> int) -> ?eqs:poly list -> ?ineqs:poly list -> ?impls: impl list -> unit -> cone

    (** Same as [make_cone] but uses the equations and order from the given ideal. *)
    val make_cone_i : ?sat:int -> ?ineqs:poly list -> ?impls:impl list -> ideal -> cone

    (*(** Tests whether it is implied that the first argument is non-negative assuming the equations and inequalities given by the cone. *)
    val is_non_neg : poly -> cone -> bool*)

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

  include (Cone with type poly := PQ.poly and type monic_mon := PQ.monic_mon and type ideal := IdealQ.ideal)

  val ppc : Format.formatter -> cone -> unit [@@ocaml.toplevel_printer]

end