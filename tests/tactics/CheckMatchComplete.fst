module CheckMatchComplete

open FStar.Tactics.V2

let guard (b:bool) =
  if not b then
    fail "guard failed"

let test_wild () : Tac unit =
  let pat = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let (r, _) = check_match_complete e (`1) (`int) [pat] in
  guard (Some? r)
let _ = assert True by (test_wild ())

let test_const_ok () : Tac unit =
  let pat = Reflection.V2.Pat_Constant (C_Int 1) in
  let e = cur_env () in
  let (r, _) = check_match_complete e (`1) (`int) [pat] in
  guard (Some? r)
let _ = assert True by (test_const_ok ())

let test_const_bad () : Tac unit =
  let pat = Reflection.V2.Pat_Constant (C_Int 2) in
  let e = cur_env () in
  let (r, _) = check_match_complete e (`1) (`int) [pat] in
  guard (None? r)
let _ = assert True by (test_const_bad ())

let test_const_two () : Tac unit =
  let pat1 = Reflection.V2.Pat_Constant (C_Int 1) in
  let pat2 = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let (r, _) = check_match_complete e (`1) (`int) [pat1; pat2] in
  guard (Some? r)
let _ = assert True by (test_const_two ())

let test_const_two' () : Tac unit =
  let pat1 = Reflection.V2.Pat_Constant (C_Int 2) in
  let pat2 = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let (r, _) = check_match_complete e (`1) (`int) [pat1; pat2] in
  guard (Some? r)
let _ = assert True by (test_const_two' ())

let test_machine_const () : Tac unit =
  let e = cur_env () in
  let i32 = Reflection.V2.Pat_Constant (C_MachineInt 1 Signed Int32) in
  let u32 = Reflection.V2.Pat_Constant (C_MachineInt 1 Unsigned Int32) in
  let wrong = Reflection.V2.Pat_Constant (C_MachineInt 1 Signed Int64) in
  let (i32_result, _) = check_match_complete e (`1l) (`Int32.t) [i32] in
  let (u32_result, _) = check_match_complete e (`1ul) (`UInt32.t) [u32] in
  let (wrong_result, _) = check_match_complete e (`1l) (`Int32.t) [wrong] in
  guard (Some? i32_result);
  guard (Some? u32_result);
  guard (None? wrong_result)
let _ = assert True by (test_machine_const ())
