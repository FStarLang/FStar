let () =
  let (_ : Prims.int) = Native_runtime.example_Effects_NativeRuntime_early true in
  if not (Native_runtime.example_Effects_NativeRuntime_test ()) then
    failwith "native Pulse exception regression";
  print_endline "native exceptions: all execution checks passed"
