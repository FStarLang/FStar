module IntLiterals

/// Integer literals are stored as their mathematical value plus a *sealed*
/// base (see FStar.IntegerLiteral). The base is presentational only: it must
/// never be observable in the logical fragment, since 0x10 and 16 denote the
/// same integer and the compiler, the normalizer and the SMT solver all treat
/// them as the same constant.

open FStar.Tactics.V2
module RD = FStar.Stubs.Reflection.V2.Data
module RB = FStar.Stubs.Reflection.V2.Builtins

(* Literals in every base the lexer accepts denote the right value, and are
   equal to their decimal counterparts even without the SMT solver. *)
#push-options "--no_smt"
let _ = assert_norm (0x10 == 16)
let _ = assert_norm (0o20 == 16)
let _ = assert_norm (0b10000 == 16)
let _ = assert_norm (007 == 7)
let _ = assert_norm ((0x10 = 16) == true)
let _ = assert_norm ((1 = 2) == false)

let f (x:int) : int = match x with | 0x10 -> 1 | 007 -> 2 | _ -> 3
let _ = assert_norm (f 16 == 1)
let _ = assert_norm (f 7 == 2)
#pop-options

(* The base is faithfully recorded, and readable by a metaprogram. *)
let base_to_string (b : FStar.IntegerLiteral.int_base) : string =
  match b with
  | Dec -> "Dec" | Hex -> "Hex" | Oct -> "Oct" | Bin -> "Bin"

let check_base (t : term) (expected : string) : Tac unit =
  match RB.inspect_ln t with
  | RD.Tv_Const (C_Int _ b) ->
    if base_to_string (unseal b) <> expected then
      fail ("expected base " ^ expected ^ ", got " ^ base_to_string (unseal b))
  | _ -> fail "not an integer literal"

let _ = assert True by (check_base (`16) "Dec")
let _ = assert True by (check_base (`0x10) "Hex")
let _ = assert True by (check_base (`0o20) "Oct")
let _ = assert True by (check_base (`0b10000) "Bin")

(* But the base is sealed, hence provably irrelevant: two literals with the
   same value are *the same term*, whatever base they were written in. This is
   what keeps FStar.Reflection.TermEq.term_eq sound. *)
let _ = assert (RB.pack_ln (RD.Tv_Const (C_Int 16 (FStar.Sealed.seal Hex))) ==
                RB.pack_ln (RD.Tv_Const (C_Int 16 (FStar.Sealed.seal Dec))))
        by (FStar.Sealed.sealed_singl
              (FStar.Sealed.seal Hex)
              (FStar.Sealed.seal #FStar.IntegerLiteral.int_base Dec);
            trefl ())

(* Machine integer literals are range-checked by the typechecker, not by the
   syntax type, so constants forged through the reflection API are checked too. *)
[@@expect_failure]
let out_of_range : FStar.UInt8.t =
  _ by (exact (RB.pack_ln (RD.Tv_Const
                (C_MachineInt 300 (FStar.Sealed.seal Dec) Unsigned Int8))))

let in_range : FStar.UInt8.t =
  _ by (exact (RB.pack_ln (RD.Tv_Const
                (C_MachineInt 255 (FStar.Sealed.seal Hex) Unsigned Int8))))

let _ = assert (FStar.UInt8.v in_range == 255)
