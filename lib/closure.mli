
module Make(P : Poly.Polynomial) : ( sig

  type poly = P.poly

  type monic_mon = P.monic_mon

  type closure

  val make : ?use_fgb:bool -> P.C.coef Sigs.Expr.expr list -> P.C.coef Sigs.Expr.expr list -> P.V.t list -> closure * poly list

  val add_eqs : poly list -> closure -> closure

  val get_ord : closure -> (monic_mon -> monic_mon -> int)

  val reduce : poly -> closure -> poly * bool

  val pp_c : Format.formatter -> closure -> unit

  val unpurify : poly -> closure -> P.C.coef Sigs.Expr.expr

  val instantiate_impls : closure -> (poly * poly) list

  val instantiate_ineqs : closure -> poly list

  val get_generators : closure -> poly list

  end)