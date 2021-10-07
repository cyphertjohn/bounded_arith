(** Module used to manipulate expressions involving Floors and Divisions *)

(** Automatically simplify an expression. See Joel S. Cohen {i Computer Algebra and Symbolic Computation:Mathematical Methods} for more details. *)
val simplify : Sigs.Q.coef Sigs.Expr.expr -> Sigs.Q.coef Sigs.Expr.expr

(** Distributes multiplication and integer powers of sumes out within an expression. E.g (x+y)(w+z) -> xw + xz + yw +yz, and (x+y)^2 -> x^2 + 2xy + y^2. *)
val distribute : Sigs.Q.coef Sigs.Expr.expr -> Sigs.Q.coef Sigs.Expr.expr

(** Parses a string as an expression. Spaces and ...)(... are intepreted as multiplication.*)
val from_string : string -> Sigs.Q.coef Sigs.Expr.expr

(** Converts an expression to a string. *)
val to_string : Sigs.Q.coef Sigs.Expr.expr -> string

val pp : Format.formatter -> Sigs.Q.coef Sigs.Expr.expr -> unit [@@ocaml.toplevel_printer]