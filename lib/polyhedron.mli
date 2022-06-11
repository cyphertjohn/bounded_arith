


module Make (C : Sigs.Coefficient) :
sig

  type lterm = C.coef BatMap.Make(Int).t * C.coef

  val pp_l : Format.formatter -> lterm -> unit

  type polyhedron

  val pp : Format.formatter -> polyhedron -> unit

  val add_cnstr : [<`eq | `ge | `gt] -> polyhedron -> lterm -> polyhedron

  val meet : polyhedron -> polyhedron -> polyhedron

  val top_p : polyhedron

  val cntsr_to_z3 : [<`eq | `ge | `gt] -> Z3.context -> lterm -> Z3.Expr.expr

  val poly_to_z3 : Z3.context -> polyhedron -> Z3.Expr.expr

  val convex_hull : Z3.context -> Z3.Solver.solver -> int list -> polyhedron

  val saturate : Z3.context -> Z3.Solver.solver -> lterm list -> lterm list -> lterm list -> Z3.Expr.expr -> int list * lterm list * lterm list

  val saturate_c : Z3.context -> Z3.Solver.solver -> lterm list -> lterm list -> lterm list -> Z3.Expr.expr -> lterm list -> int list * lterm list * lterm list

  val optimize_t_by_project : lterm -> int -> int list -> polyhedron -> Z3.context -> Z3.Solver.solver -> lterm list * lterm list

end