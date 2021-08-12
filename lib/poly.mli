(** Polynomial operations. *)

open Sigs.Polynomial

(** A default lexicographic order. *)
val lex_ord : monic_mon -> monic_mon -> int

(** A default graded lexicographic order. *)
val grlex_ord : monic_mon -> monic_mon -> int

(** A functor for manipulating polynomials whose coeficients functions are given as input. *)
module Make :
  functor (C : Sigs.Coefficient) ->
  sig
    
    (**A function to set the monomial order. On initialization, a lex order is used.*)
    val set_ord :
      (monic_mon -> monic_mon -> int) -> unit

    (**Computes the sum of two polynomials. *)
    val add :
      C.coef polynomial -> C.coef polynomial -> C.coef polynomial

    (** Multiplies two polynomials. *)
    val mult :
      C.coef polynomial -> C.coef polynomial -> C.coef polynomial
    
    (** Exponentiates a polynomial to some integer power.*)
    val exp_poly : C.coef polynomial -> int -> C.coef polynomial

    (** Uses the multivariate division algorithm to divide a polynomial a list of divisors. 
    The result is a pair where the first element is a list of multiples of the divisors and the second element is the remainder.*)
    val division : C.coef polynomial list -> C.coef polynomial -> C.coef polynomial list * C.coef polynomial

    (** Computes a Grobner basis. *)
    val improved_buchberger : C.coef polynomial list -> C.coef polynomial list

    (** [substitute (x, p) q] substitutes [p] for every occurrence of [x] in [q].*)
    val substitute :
      string * C.coef polynomial -> C.coef polynomial -> C.coef polynomial

    (** Test if a polynomial is zero. *)
    val is_zero : C.coef polynomial -> bool

    (** Polynomial comparison. The result does not correspond to any arithmetic order.*)
    val compare : C.coef polynomial -> C.coef polynomial -> int
    
    (** Parses a string as a polynomial. *)
    val from_string : string -> C.coef polynomial

    (** Converts a polynomial to a string. *)
    val to_string : C.coef polynomial -> string

    (** The constant -1 as a polynomial. *)
    val minus_1 : C.coef polynomial

  end
