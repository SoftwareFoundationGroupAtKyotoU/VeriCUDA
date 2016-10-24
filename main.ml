open Vc
open Print
open Verifier

let usage_msg : Arg.usage_msg = "<program> [options] filename funcname"
let outname = ref ""
let filename = ref ""
let funcname = ref ""

(* ---------------- process command line arguments *)
let spec_list = [
  ("--output", Arg.Set_string outname,
   "Output directory; Coq files are output to this directory");
  ("--check-race", Arg.Set check_race_freedom,
   "Generate VC for race-freedom");
  ("--check-diverge", Arg.Set check_barrier_divergence,
   "Generate VC for barrier-divergence-freedom");
  ("--print-exception", Arg.Set print_exn_flag,
   "Pretty print some exceptions");
  ("--debug", Arg.Set Utils.debug_flag, "Print debug messages");
  ("--warning", Arg.Set Utils.warn_flag, "Print warnings");
  (* ("--print-task", Arg.Set print_task_flag, "Print generated tasks"); *)
  ("--print-task-style",
   Arg.String (fun s -> print_task_style := s),
   "full, short, or none");
  ("--no-proof", Arg.Clear prove_flag,
   "Do not try to prove generated tasks");
  ("--no-transform", Arg.Clear trans_flag,
   "Do not transform generated tasks");
  ("--timelimit", Arg.Set_int default_timelimit,
   "Timelimit for each prover call (in sec)");
  ("--memlimit",Arg.Set_int default_memlimit,
   "Memory limit for each prover call (in MB)");
  ("--interactive", Arg.Set interactive_flag, "interactive mode");
  ("--no-inline", Arg.Clear inline_assignment,
   "Do not inline `assign' predicate");
  ("--print-size", Arg.Set print_size_flag, "print size of tasks");
  (* always use logical operators *)
  (* ("--logical-operator", Arg.Set Cil.useLogicalOperators, "use logical operator"); *)
  ("--parse-only", Arg.Set parse_only_flag,
   "print the result of parsing and exit");
  ("--use-triggers", Arg.Set Formula.use_triggers_flag,
   "use triggers");
]

let anon_fun str =
  if !filename = "" then filename := str
  else if !funcname = "" then funcname := str
  else raise (Arg.Bad ("Too many arguments: " ^ str))

let verify filename funcname =
  if !print_exn_flag then
    try
      verify_spec filename funcname
    with
      e -> print_exception e
  else
    verify_spec filename funcname

let verify_interactive filename funcname =
  Format.printf "interactive mode@.";
  let tasks = generate_task filename funcname in
  Format.printf "generated %d tasks@." (List.length tasks);
  Interactive.start_repl tasks

let () =
  Cil.useLogicalOperators := true;
  Arg.parse spec_list anon_fun usage_msg;
  Why3.Whyconf.load_plugins @@ Why3.Whyconf.get_main Why3api.config;
  Why3.Warning.set_hook (fun ?loc _ -> ());
  if !outname <> "" then
    begin
      let tasks = generate_task !filename !funcname in
      List.iter (Why3util.output_coq_of_task !outname) tasks;
      exit 0
    end;
  if !interactive_flag then
    verify_interactive !filename !funcname
  else
    verify !filename !funcname
