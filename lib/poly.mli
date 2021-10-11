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

  (** Initialize a polynomial from a constant *)
  val from_const : C.coef -> poly

  val pp : Format.formatter -> poly -> unit [@@ocaml.toplevel_printer]

  end

(** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
module Ideal :
  functor (C : Sigs.Coefficient) -> 
  sig

    (** An ideal of polynomial generators p_1, ..., p_n, is the set of polynomials f such that f = a_1p_1 + ... + a_np_n
    for polynomials a_1, ..., a_n *)
    type ideal

    (** An empty ideal (<0>) initialized with a monomial order.*)
    val initialize : (Make(C).monic_mon -> Make(C).monic_mon -> int) -> ideal

    (** Add polynomials to the ideal. *)    
    val add_polys : Make(C).poly list -> ideal -> ideal

    (** Reduce a polynomial by an ideal. That is [reduce p i], returns r, i', such that p = f + r, 
    with r minimum in the monomial order. [reduce] also returns [i] as [i'] which represents the same ideal,
    but could be represented differently internally. I.e. reduce will compute a grobner basis if one hasn't
    already been computed.*)
    val reduce : Make(C).poly -> ideal -> Make(C).poly * ideal

  end

(** A (linear) cone consists of an ideal, representing equations, and all positive linear combinations of a set of inequalities.
    Thus, each polynomial in the cone represents a positive polynomial. *)
module Cone :
  functor (C : Sigs.Coefficient) -> 
  sig

    (** A (linear) cone consists of an ideal, representing equations, and all positive linear combinations of a set of inequalities.
    Thus, each polynomial in the cone represents a positive polynomial. *)
    type cone

    (** An empty cone <0> intialized with a monomial order. *)
    val initialize : ?sat:int -> (Make(C).monic_mon -> Make(C).monic_mon -> int) -> cone

    (** Add equations to the cone. *)
    val add_eqs : Make(C).poly list -> cone -> cone

    (** Add inequalities to the cone. *)
    val add_ineqs : Make(C).poly list -> cone -> cone

    (** Reduce a polynomial by a cone. That is [reduce p i], returns r, i', such that p = f + r, 
    with the leading term of r minimum in the monomial order. If the inequalities, q_i in the cone were assumed to be
    non-negative, then f is also non-negative. Therefore, p >= r. If the inequalities were assumed to be non-positive then p <= r.*)
    val reduce : Make(C).poly -> cone -> Make(C).poly * cone

    (** Reduce a polynomial by a cone only using the equations of the cone. *)
    val reduce_eq : Make(C).poly -> cone -> Make(C).poly * cone
  end