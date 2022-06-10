module PolyQ = Poly.Make(Sigs.Q)(Sigs.V)
module ConeQ = Cone.Make(PolyQ)
module CongQ = Closure.Make(PolyQ)


(** Compute an upper bound for t over the variables in vars_to_keep,
    provided the equalities tx = 0 for all tx in terms. *)
let rewrite ?sat:(sat=3) ?fgb:(fgb=true) (eqs : Expr.qexpr list) (ineqs : Expr.qexpr list) vars_to_keep (ts : Expr.qexpr list) = 
  let cl, pure_polys = CongQ.make ~use_fgb:fgb eqs (ts @ ineqs) (List.map Sigs.V.of_string vars_to_keep) in
  Log.log_line_s ~level:`debug "Initial Closure map";
  Log.log ~level:`debug CongQ.pp_c (Some cl);
  let ts_pure, ineqs_pure = List.partition (fun (i, _) -> i < List.length ts) (List.mapi (fun i a -> (i, a)) pure_polys) in
  let const_ts, non_consts_ts = List.partition (fun (_, t) -> match PolyQ.is_const t with | None -> false | Some _ -> true) ts_pure in
  let rewritten_ts = 
    let const_ts_ups_and_lows = List.map (fun (i, const_t) -> i, ([const_t], [const_t])) const_ts in
    if non_consts_ts = [] then const_ts_ups_and_lows
    else
      let cone = ConeQ.make_cone_cl ~sat:sat ~ineqs:(List.map snd ineqs_pure) ~impls:[] cl in
      Log.log_line_s ~level:`debug "After Cone saturation";
      Log.log ~level:`debug ConeQ.ppc (Some cone);
      let rewritten_non_consts = List.map (fun (i, t) -> i, ConeQ.reduce t cone) non_consts_ts in
      rewritten_non_consts @ const_ts_ups_and_lows
  in
  let sorted_bounds = List.sort (fun (i, _) (j, _) -> compare i j) rewritten_ts in
  let unpurify_bounds bs = List.map (fun b -> Expr.simplify (CongQ.unpurify b cl)) bs in
  List.map (fun (_, (ups, lows)) -> unpurify_bounds ups, unpurify_bounds lows) sorted_bounds