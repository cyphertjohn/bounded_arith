module SymBoundBenchmark = struct
  let usage_msg = "[-sat] [-hull]"
  let _sat_bound = ref 3
  let _compute_hull = ref false

  let sat_bound () = !_sat_bound
  let compute_hull () = !_compute_hull

  let speclist =
    [
      ("-sat", Arg.Set_int _sat_bound, "Set product saturation bound");
      ("-hull", Arg.Set _compute_hull, "Set whether to compute convex hull");
    ]

  let process_cmdline () = Arg.parse speclist (fun _ -> ()) usage_msg
end