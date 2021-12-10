let level_leq x y = 
  let to_int = function
    | `trace -> 0
    | `debug -> 1
    | `always -> 2
  in
  (to_int x) <= (to_int y)

let my_level = ref `always
let log_times = ref false
let f = ref (Format.std_formatter)

module StrMap = Map.Make(String)
let label_map = ref StrMap.empty

let set_formatter fo = 
  f := fo

let set_level lev = 
  match lev with
  | "trace" -> my_level := `trace
  | "debug" -> my_level := `debug
  | "always" -> my_level := `always
  | _ -> failwith "Unrecognized Level"

let log ?(level=`always) pp obj = 
  if level_leq !my_level level then
    Format.pp_print_option (fun fo o -> pp fo o; Format.pp_print_newline fo ()) !f obj
  else
    ()


let log_s ?(level=`always) str = 
  if level_leq !my_level level then
    Format.fprintf !f "@[%s@]" str
  else
    Format.ifprintf !f "@[%s@]" str;
  Format.pp_print_flush !f ()
      
let log_line_s ?(level=`always) str = 
  if level_leq !my_level level then
    (Format.fprintf !f "@[%s@]" str;
    Format.pp_print_newline !f ())
  else
    (Format.ifprintf !f "@[%s@]" str;
    Format.pp_print_flush !f ())
  

let log_time label fu arg = 
  let start_time = Unix.gettimeofday () in
  let res = fu arg in
  let tim = Unix.gettimeofday () -. start_time in
  let _ = 
    if !log_times then (Format.fprintf !f "@[%s: %f s@]" label tim; Format.pp_print_newline !f ())
    else (Format.ifprintf !f "@[%s: %f s@]" label tim; Format.pp_print_flush !f ())
  in
  res

let update_tim label tim =
  match (StrMap.find_opt label !label_map) with
  | None -> label_map := StrMap.add label tim !label_map
  | Some y -> label_map := StrMap.add label (tim +. y) (StrMap.remove label !label_map)


let log_time_cum label fu arg = 
  let start_time = Unix.gettimeofday () in
  let res = fu arg in
  let tim = Unix.gettimeofday () -. start_time in
  update_tim label tim;
  let _ = 
    if !log_times then (Format.fprintf !f "@[%s: %f s@]" label (StrMap.find label !label_map); Format.pp_print_newline !f ())
    else (Format.ifprintf !f "@[%s: %f s@]" label tim; Format.pp_print_flush !f ())
  in
  res
