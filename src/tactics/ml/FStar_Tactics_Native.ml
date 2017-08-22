open FStar_Tactics_Builtins
open FStar_Tactics_Derived
open FStar_Tactics_Logic

open FStar_Syntax_Syntax
open FStar_Range

module E = FStar_Tactics_Effect
module B = FStar_Tactics_Basic
module BU = FStar_Util

let r = dummyRange

type itac = B.proofstate -> args -> term option
type native_primitive_step =
    { name: FStar_Ident.lid;
      arity: Prims.int;
      strong_reduction_ok: bool;
      tactic: itac}

let compiled_tactics: native_primitive_step list ref = ref []

let list_all () = !compiled_tactics

let is_native_tactic lid =
    BU.is_some (BU.try_find (fun x -> FStar_Ident.lid_equals lid x.name) !compiled_tactics)

let register_tactic (s: string) (arity: int) (t: itac)=
    let step =
        { name=FStar_Ident.lid_of_str s;
          arity = Z.of_int arity;
          strong_reduction_ok=false;
          tactic=t } in
    compiled_tactics := step :: !compiled_tactics;
    BU.print1 "Registered tactic %s\n" s

let interpret_tactic (ps: B.proofstate) (t: B.proofstate -> 'a E.__result) =
    match t ps with
    | E.Success (a, state) -> B.Success (a, state)
    | E.Failed (s, state) -> B.Failed (s, state)

let from_tactic_0 (t: 'b E.tactic): ('b B.tac) =
    (fun (ps: B.proofstate) ->
        print_string "In compiled code\n";
        let m = t () in
        interpret_tactic ps m) |> B.mk_tac

let from_tactic_1 (t: 'a -> 'b E.tactic): ('a -> 'b B.tac) =
    fun (x: 'a) ->
        (fun (ps: B.proofstate) ->
            print_string "In compiled code\n";
            let m = t x in
            let (m2: B.proofstate -> 'b E.__result) = m () in
            interpret_tactic ps m2) |> B.mk_tac

let from_tactic_2 (t: 'a -> 'b -> 'c E.tactic): ('a -> 'b -> 'c B.tac) =
    fun (x: 'a) ->
        fun (y: 'b) ->
            (fun (ps: B.proofstate) ->
                print_string "In compiled code\n";
                let m = t x y in
                let (m2: B.proofstate -> 'c E.__result) = m () in
                interpret_tactic ps m2) |> B.mk_tac