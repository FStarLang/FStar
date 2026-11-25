let () =
  (* Native functions return ordinary outcome data at their boundary. Its
     defining unit differs between whole-program and split extraction, so
     select the constructors by type. *)
  (match[@warning "-40"] Native_runtime.example_Effects_NativeRuntime_early true,
         Native_runtime.example_Effects_NativeRuntime_early false with
   | Pulse_Lib_Effects_Rules_Normal x, Pulse_Lib_Effects_Rules_Raised e
     when Z.equal x (Z.of_int 7) && Z.equal e (Z.of_int 9) -> ()
   | _ -> failwith "native Pulse outcome ABI regression");
  if not (Native_runtime.example_Effects_NativeRuntime_test ()) then
    failwith "native Pulse exception regression";
  let trace = ref [] in
  let note tag = trace := tag :: !trace in
  if not (Native_runtime.example_Effects_NativeRuntime_stress note) then
    failwith "native Pulse exception stress regression";
  let expected =
    [100; 2; 1; 101; 2; 1; 102; 2; 1; 200; 3; 5; 4; 5; 201; 8; 7; 300]
    @ List.init 257 Fun.id @ [400] @ List.init 1000 (fun _ -> 6)
    |> List.map Stdint.Uint32.of_int
  in
  if List.rev !trace <> expected then
    failwith "native Pulse cleanup order/count regression";
  print_endline "native exceptions: all execution checks passed"
