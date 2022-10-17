
  let usage_msg = "[-v <trace | debug >] [-sat <depth>] [-lp] <smt>"
  let _sat_bound = ref 3
  let _use_lp = ref false

  let speclist =
    [
      ("-v", Arg.String Bound.Log.set_level, "Set verbosity. Levels are trace, debug, and always");
      ("-sat", Arg.Set_int _sat_bound, "Set product saturation bound");
      ("-lp", Arg.Set _use_lp, "Set whether to use lp to compute bounds instead of projection");
      ("-t", Arg.Set Bound.Log.log_times, "Output time")
    ]

  let smt_file = ref ""

  let set_file s = smt_file := s

  let () = 
    Arg.parse speclist set_file usage_msg;
    let rewrite smt = Bound.Rewriter.rewrite_rba ~sat:(!_sat_bound) ~use_proj:(not !_use_lp) smt in
    let (tups, tlows) = Bound.Log.log_time "total" rewrite !smt_file in
    Bound.Log.log_line_s "__cost upper bounds";
    List.iter (fun u -> Bound.Log.log (Bound.Expr.pp) (Some u)) tups;
    Bound.Log.log_line_s "";
    Bound.Log.log_line_s "__cost lower bounds";
    List.iter (fun l -> Bound.Log.log (Bound.Expr.pp) (Some l)) tlows