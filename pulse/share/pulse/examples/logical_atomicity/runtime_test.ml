(**
   Executable regressions for extracted logical-atomicity examples.

   The F* sources prove resource/abstract-state contracts; these tests check
   extraction, native realization, and representative schedules. This OCaml
   harness itself is not verified: erased ownership preconditions are
   respected by its test construction rather than enforced by OCaml types.

   Sequential checks cover counter wraparound, failed CAS, read-only
   commitment, and descriptor helping. The msqueue/ and concurrent_set/
   directories contain separate native harnesses for their larger examples.
   These checks are not a weak-memory validation or a liveness proof.
*)

(** Parse through the extracted integer API to avoid host-int range assumptions. *)
let u32 n = FStar_UInt32.uint_to_t (Prims.parse_int n)
(** Executable numeric parameter retained by counter extraction; the actual
   later-credit ownership is ghost and is not supplied by this OCaml value. *)
let credits = Prims.int_one

(** Run bounded regressions and fail on any violated observation. Native task
   teardown currently leaves workers running; process exit bounds these
   helper tests' pool lifetimes. *)
let () =
  let r, old = Counter.pulse_Lib_LogicalAtomicity_Example_Counter_client_once () in
  assert (old = u32 "0" && !r = u32 "1");
  let old = Counter.pulse_Lib_LogicalAtomicity_Example_Counter_fetch_add r credits () in
  assert (old = u32 "1" && !r = u32 "2");

  let r = ref (u32 "8") in
  assert (not (Counter.pulse_Lib_LogicalAtomicity_Example_Counter_try_attempt r credits (u32 "7")));
  assert (!r = u32 "8");
  assert (Counter.pulse_Lib_LogicalAtomicity_Example_Counter_try_attempt r credits (u32 "8"));
  assert (!r = u32 "9");

  let r = ref (u32 "4294967295") in
  let old = Counter.pulse_Lib_LogicalAtomicity_Example_Counter_fetch_add r credits () in
  assert (old = u32 "4294967295" && !r = u32 "0");

  let r, value = Read.pulse_Lib_LogicalAtomicity_Example_Read_client () in
  assert (value = u32 "37" && !r = u32 "37");
  assert (Read.pulse_Lib_LogicalAtomicity_Example_Read_read r () = u32 "37");
  assert (!r = u32 "37");
  for _ = 1 to 32 do
    let r, old = Helping.pulse_Lib_LogicalAtomicity_Example_Helping_two_helpers () in
    assert (old = u32 "0" && !r = u32 "1")
  done;
  print_endline "Logical atomicity extraction tests passed"
