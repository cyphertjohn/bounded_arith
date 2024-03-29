


module Make (C : Sigs.Coefficient)(V : Sigs.Var) :
sig

  type lterm = C.coef V.M.map * C.coef

  val pp_l : Format.formatter -> lterm -> unit

  type polyhedron

  val pp : Format.formatter -> polyhedron -> unit

  val add_cnstr : [<`eq | `ge | `gt] -> polyhedron -> lterm -> polyhedron

  val meet : polyhedron -> polyhedron -> polyhedron

  val top_p : polyhedron

  val get_size : polyhedron -> int * int

  val cntsr_to_z3 : [<`eq | `ge | `gt] -> Z3.context -> lterm -> Z3.Expr.expr

  val poly_to_z3 : Z3.context -> polyhedron -> Z3.Expr.expr

  (*val convex_hull : Z3.context -> Z3.Solver.solver -> polyhedron*)

  val saturate_c : Z3.context -> Z3.Solver.solver -> lterm list -> lterm list -> lterm list -> Z3.Expr.expr -> lterm Sigs.Form.form list -> int list * lterm list * lterm list * lterm list

  val optimize_t : ?use_proj:bool -> lterm -> V.v -> V.v list -> polyhedron -> Z3.context -> Z3.Solver.solver -> lterm list * lterm list

end