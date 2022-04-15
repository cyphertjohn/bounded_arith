
module Make(P : Poly.Polynomial) :
  sig

    type cone

    type poly = P.poly

    type impl = poly * poly

    val (=>) : poly -> poly -> impl

    val make_cone_cl : ?sat:int -> ?ineqs:(poly list) -> ?impls:impl list -> Closure.Make(P).closure -> cone

    val unpurify : poly -> cone -> P.C.coef Sigs.Expr.expr

    val reduce : poly -> cone -> poly

    val ppc : Format.formatter -> cone -> unit
    
end
 