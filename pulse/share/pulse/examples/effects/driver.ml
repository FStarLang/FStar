(* Executable harness for Example.Effects.Runtime, not an effect implementation.
   The Makefile extracts that module into Effects_runtime.ml and links this
   small OCaml entry point against it. The returned list contains five concrete
   comparisons, covering ordinary operations, raised/normal exceptions, and
   both nested routes. A mismatch raises an OCaml exception and fails make.
   This harness is external to the Pulse proof; it checks the extracted result. *)

(* Require both the expected number of observations and success of each one.
   Checking the entire list also detects an accidentally omitted runtime case.
   Print success only after the extracted entry point and all comparisons pass. *)
let () =
  let checks = Effects_runtime.example_Effects_Runtime_test () in
  if checks <> [true; true; true; true; true] then
    failwith "effects: state transfer, exception handling, or forwarding failed";
  print_endline "effects: all five execution checks passed"
