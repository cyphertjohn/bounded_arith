module PolyQ = Poly.Make(Sigs.Q)(Sigs.V)
module ConeQ = Cone.Make(PolyQ)
module CongQ = Closure.Make(PolyQ)


(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite ?sat:(sat=3) ?(use_proj=true) ?fgb:(fgb=true) ?(compute_hull=false) (eqs : Expr.qexpr list) (ineqs : Expr.qexpr list) vars_to_keep (ts : Expr.qexpr list) = 
  let mk_cone vs =   
    let cl, pure_polys = CongQ.make ~use_fgb:fgb eqs (ts @ ineqs) (List.map Sigs.V.of_string vs) in
    Log.log_line_s ~level:`debug "Initial Closure map";
    Log.log ~level:`debug CongQ.pp_c (Some cl);
    let ts_pure, ineqs_pure = List.partition (fun (i, _) -> i < List.length ts) (List.mapi (fun i a -> (i, a)) pure_polys) in
    let const_ts, non_consts_ts = List.partition (fun (_, t) -> match PolyQ.is_const t with | None -> false | Some _ -> true) ts_pure in
    if non_consts_ts = [] then const_ts, non_consts_ts, ConeQ.make_cone_cl cl, cl
    else
      let c = ConeQ.make_cone_cl ~sat:sat ~ineqs:(List.map snd ineqs_pure) ~impls:[] ~hull:compute_hull cl in
      Log.log_line_s ~level:`debug "After Cone saturation";
      Log.log ~level:`debug ConeQ.ppc (Some c);
      const_ts, non_consts_ts, c, cl
    in
  let pure_consts, pure_non_consts, con, cl = Log.log_time "Construct cone" mk_cone vars_to_keep in
  let rewrite c = 
    let const_ts_ups_and_lows = List.map (fun (i, const_t) -> i, ([const_t], [const_t])) pure_consts in
    if pure_non_consts = [] then const_ts_ups_and_lows
    else 
      let rewritten_non_consts = List.map (fun (i, t) -> i, ConeQ.reduce ~use_proj:use_proj t c) pure_non_consts in
      rewritten_non_consts @ const_ts_ups_and_lows
  in
  let rewritten_ts = Log.log_time "Reducing" rewrite con in
  let sorted_bounds = List.sort (fun (i, _) (j, _) -> compare i j) rewritten_ts in
  let unpurify_bounds bs = List.map (fun b -> Expr.simplify (CongQ.unpurify b cl)) bs in
  List.map (fun (_, (ups, lows)) -> unpurify_bounds ups, unpurify_bounds lows) sorted_bounds



(*
module P = Polyhedron.Make(Sigs.Q)(Sigs.V)

let rewrite_linear smt vars_to_keep (ts : Expr.qexpr list) = 
  let ctx = Z3.mk_context [] in
  let form = Z3.Boolean.mk_and ctx (Z3.AST.ASTVector.to_expr_list (Z3.SMT.parse_smtlib2_file ctx smt [] [] [] [])) in
  
  let p = P.convex_hull ctx 
  *)