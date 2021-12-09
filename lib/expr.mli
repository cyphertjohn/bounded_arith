(** Module used to manipulate expressions involving Floors and Divisions *)

type qexpr = Sigs.Q.coef Sigs.Expr.expr

val from_const : Sigs.Q.coef -> qexpr

val from_var : string -> int -> qexpr

val add : qexpr -> qexpr -> qexpr

val negate : qexpr -> qexpr

val minus : qexpr -> qexpr -> qexpr

val mult : qexpr -> qexpr -> qexpr

val exp : qexpr -> int -> qexpr

val div : qexpr -> qexpr -> qexpr

val floor : qexpr -> qexpr

(** Automatically simplify an expression. See Joel S. Cohen {i Computer Algebra and Symbolic Computation:Mathematical Methods} for more details. *)
val simplify : qexpr -> qexpr

(** Distributes multiplication and integer powers of sumes out within an expression. E.g (x+y)(w+z) -> xw + xz + yw +yz, and (x+y)^2 -> x^2 + 2xy + y^2. *)
val distribute : qexpr -> qexpr

(** Parses a string as an expression. Spaces and ...)(... are intepreted as multiplication.*)
val from_string : string -> qexpr

(** Converts an expression to a string. *)
val to_string : qexpr -> string

val pp : Format.formatter -> qexpr -> unit [@@ocaml.toplevel_printer]