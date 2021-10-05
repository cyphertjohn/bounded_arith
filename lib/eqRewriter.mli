(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms, and inequalities qx<= 0. *)
val rewrite : Sigs.Q.coef Sigs.Expr.expr list -> Sigs.Q.coef Sigs.Expr.expr list -> string list -> Sigs.Q.coef Sigs.Expr.expr -> Sigs.Q.coef Sigs.Expr.expr
