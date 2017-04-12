
(* TODO : this file does not have the same interface as platform.fsi *)

let exe name =
  if Sys.unix then
    name
  else
    name^".exe"

let is_fstar_compiler_using_ocaml = true

let init_print_ocaml_gc_statistics () =
  let pid = Unix.getpid () in
  prerr_string "Starting F* as process: ";
  prerr_int pid;
  prerr_string "; command line:";
  let argv = Sys.argv in
  let argc = Array.length argv in
  let rec build_cmdline accu i =
    if i = argc
    then accu
    else build_cmdline (Format.sprintf "%s %s" accu argv.(i)) (i + 1)
  in
  let cmdline = build_cmdline "" 0 in
  prerr_endline cmdline;
  ignore (Gc.create_alarm (fun () -> (
    prerr_string "Reporting for process: ";
    prerr_int pid;
    prerr_string "; command line:";
    prerr_string cmdline;
    prerr_string "\n";
    (* NOTE: we do not use prerr_newline here, to avoid flushing stdout here;
       useful if several instances of F* are run in parallel *)
    Gc.print_stat stderr;
    prerr_newline () (* flush here *)
  )))
