module CheckMatchComplete

open FStar.Tactics.V2

let guard (b:bool) =
  if not b then
    fail "guard failed"

let test_wild () : Tac unit =
  let pat = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let r = check_match_complete e (`1) (`int) [pat] in
  guard (Some? r)
let _ = assert True by (test_wild ())

let test_const_ok () : Tac unit =
  let pat = Reflection.V2.Pat_Constant (C_Int 1) in
  let e = cur_env () in
  let r = check_match_complete e (`1) (`int) [pat] in
  guard (Some? r)
let _ = assert True by (test_const_ok ())

let test_const_bad () : Tac unit =
  let pat = Reflection.V2.Pat_Constant (C_Int 2) in
  let e = cur_env () in
  let r = check_match_complete e (`1) (`int) [pat] in
  guard (None? r)
let _ = assert True by (test_const_bad ())

let test_const_two () : Tac unit =
  let pat1 = Reflection.V2.Pat_Constant (C_Int 1) in
  let pat2 = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let r = check_match_complete e (`1) (`int) [pat1; pat2] in
  guard (Some? r)
let _ = assert True by (test_const_two ())

let test_const_two' () : Tac unit =
  let pat1 = Reflection.V2.Pat_Constant (C_Int 2) in
  let pat2 = Reflection.V2.Pat_Var (Sealed.seal (`int)) (Sealed.seal "x") in
  let e = cur_env () in
  let r = check_match_complete e (`1) (`int) [pat1; pat2] in
  guard (Some? r)
let _ = assert True by (test_const_two' ())
