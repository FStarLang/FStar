let u32 n = FStar_UInt32.uint_to_t (Prims.parse_int n)
let credits = Prims.int_one

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
