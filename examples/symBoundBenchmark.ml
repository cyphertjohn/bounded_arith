module SymBoundBenchmark = struct
  let usage_msg = "[-sat <depth>] [-lp]"
  let _sat_bound = ref 3
  let _use_lp = ref false

  let sat_bound () = !_sat_bound
  let use_lp () = !_use_lp

  let speclist =
    [
      ("-sat", Arg.Set_int _sat_bound, "Set product saturation bound");
      ("-lp", Arg.Set _use_lp, "Set whether to use lp to compute bounds instead of projection");
    ]

  let process_cmdline () = Arg.parse speclist (fun _ -> ()) usage_msg
end