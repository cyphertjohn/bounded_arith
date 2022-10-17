module PolyQ = Poly.Make(Sigs.Q)(Sigs.V)
module ConeQ = Cone.Make(PolyQ)
module CongQ = Closure.Make(PolyQ)


(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite ?sat:(sat=3) ?(use_proj=true) ?fgb:(fgb=true) (eqs : Expr.qexpr list) (ineqs : Expr.qexpr list) vars_to_keep (ts : Expr.qexpr list) = 
  let mk_cone vs =   
    let cl, pure_polys = CongQ.make ~use_fgb:fgb eqs (ts @ ineqs) in
    Log.log_line_s ~level:`debug "Initial Closure map";
    Log.log ~level:`debug CongQ.pp_c (Some cl);
    let ts_pure, ineqs_pure = List.partition (fun (i, _) -> i < List.length ts) (List.mapi (fun i a -> (i, a)) pure_polys) in
    let const_ts, non_consts_ts = List.partition (fun (_, t) -> match PolyQ.is_const t with | None -> false | Some _ -> true) ts_pure in
    if non_consts_ts = [] then const_ts, non_consts_ts, ConeQ.make_cone_cl cl
    else
      let c = ConeQ.make_cone_cl ~sat:sat ~ineqs:(List.map snd ineqs_pure) ~impls:[] cl in
      let c = ConeQ.set_effective_degree c (List.map Sigs.V.of_string vs) in
      Log.log_line_s ~level:`debug "After Cone saturation";
      Log.log ~level:`debug ConeQ.ppc (Some c);
      const_ts, non_consts_ts, c
    in
  let pure_consts, pure_non_consts, con = Log.log_time "Construct cone" mk_cone vars_to_keep in
  let rewrite c = 
    let const_ts_ups_and_lows = List.map (fun (i, const_t) -> i, ([const_t], [const_t])) pure_consts in
    if pure_non_consts = [] then const_ts_ups_and_lows
    else 
      let rewritten_non_consts = List.map (fun (i, t) -> i, ConeQ.reduce ~use_proj:use_proj t c) pure_non_consts in
      rewritten_non_consts @ const_ts_ups_and_lows
  in
  let rewritten_ts = Log.log_time "Reducing" rewrite con in
  let sorted_bounds = List.sort (fun (i, _) (j, _) -> compare i j) rewritten_ts in
  let unpurify_bounds bs = List.map (fun b -> Expr.simplify (ConeQ.unpurify b con)) bs in
  List.map (fun (_, (ups, lows)) -> unpurify_bounds ups, unpurify_bounds lows) sorted_bounds

module F = Sigs.FormT(Sigs.Q)

(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite_rba ?sat:(sat=3) ?(use_proj=true) ?fgb:(fgb=true) ?(ineqs = []) smt = 
  let ctx = Z3.mk_context [] in
  let form = List.hd (Z3.AST.ASTVector.to_expr_list (Z3.SMT.parse_smtlib2_file ctx smt [] [] [] [])) in
  let form, vars_to_keep = F.z3_to_expr_form ctx form in
  Log.log_line_s ~level:`trace "vars to keep";
  Log.log ~level:`trace (Format.pp_print_list ~pp_sep:(fun fo () -> Format.pp_print_string fo "; ") Format.pp_print_string) (Some vars_to_keep);
  let mk_cone vs = 
    let expr_to_rewrite = Sigs.Expr.Var "__cost" in
    let cl, rewrite_ineqs_pure = CongQ.make ~use_fgb:fgb [] (expr_to_rewrite :: ineqs) in
    let pure_t, ineqs_pure = List.hd rewrite_ineqs_pure, List.tl rewrite_ineqs_pure in
    let pure_form, _, cl = CongQ.purify_form form cl in
    Log.log_line_s ~level:`debug "Initial Closure map";
    Log.log ~level:`debug CongQ.pp_c (Some cl);
    let c = ConeQ.make_cone_cl_form ~sat:sat ~ineqs:(ineqs_pure) pure_form cl in
    let c = ConeQ.set_effective_degree c (List.map Sigs.V.of_string vs) in
    Log.log_line_s ~level:`debug "After Cone saturation";
    Log.log ~level:`debug ConeQ.ppc (Some c);
    pure_t, c
  in
  let pure_t, con = Log.log_time "Construct cone" mk_cone vars_to_keep in

  let rewritten_t = Log.log_time "Reducing" (ConeQ.reduce ~use_proj:use_proj pure_t) con in
  let unpurify_bounds bs = List.map (fun b -> Expr.simplify (ConeQ.unpurify b con)) bs in
  unpurify_bounds (fst rewritten_t), unpurify_bounds (snd rewritten_t)

(*
module P = Polyhedron.Make(Sigs.Q)(Sigs.V)

let rewrite_linear smt vars_to_keep (ts : Expr.qexpr list) = 
  let ctx = Z3.mk_context [] in
  let form = Z3.Boolean.mk_and ctx (Z3.AST.ASTVector.to_expr_list (Z3.SMT.parse_smtlib2_file ctx smt [] [] [] [])) in
  
  let p = P.convex_hull ctx 
  *)