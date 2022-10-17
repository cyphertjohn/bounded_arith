
module Make(P : Poly.Polynomial) :
sig

  type cone

  type poly = P.poly

  type impl = poly * poly

  val (=>) : poly -> poly -> impl

  val make_cone_cl : ?sat:int -> ?ineqs:(poly list) -> ?impls:impl list -> Closure.Make(P).closure -> cone

  val make_cone_cl_form : ?sat:int -> ?ineqs:(poly list) -> poly Sigs.Form.form -> Closure.Make(P).closure -> cone

  val unpurify : poly -> cone -> P.C.coef Sigs.Expr.expr

  val reduce : ?use_proj:bool -> poly -> cone -> (poly list) * (poly list)

  val ppc : Format.formatter -> cone -> unit
  
  val set_effective_degree : cone -> P.V.v list -> cone

end
