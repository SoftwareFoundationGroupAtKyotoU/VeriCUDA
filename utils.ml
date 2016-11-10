let stderr_fmt = Format.formatter_of_out_channel stderr

let warn fmt =
  let fprintf =
    if !Options.warn_flag then Format.fprintf else Format.ifprintf
  in
  fprintf stderr_fmt "[Warning] ";
  fprintf stderr_fmt fmt

let debug fmt =
  let fprintf =
    if !Options.debug_flag then Format.fprintf else Format.ifprintf
  in
  fprintf stderr_fmt "[Debug] ";
  fprintf stderr_fmt fmt

let impl_error msg =
  output_string stderr ("implementation error\n");
  if msg <> "" then output_string stderr (" " ^ msg ^ "\n");
  exit 1


exception Not_implemented of string
exception Implementation_error of string

let not_implemented msg = raise (Not_implemented msg)

let implementation_error msg = raise (Implementation_error msg)

let time f =
  let t = Unix.gettimeofday () in
  let result = f () in
  let t' = Unix.gettimeofday () in
  (result, t' -. t)
