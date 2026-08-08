(*
   An erasable (ghost) computation may only be lifted to a non-erasable effect
   when its result type is non-informative.  `TcUtil.lift_comp` implements
   exactly that check, and the check IS still enforced for user-defined
   erasable effects -- e.g.

       [@@ erasable] total assume effect MYG
       assume sub_effect MYG ~> DIV
       assume val secret : unit -> MYG bool (requires True) (ensures fun _ -> True)
       let leak (u:unit) : Dv bool = secret ()   // correctly Error 12

   `GHOST` is the one effect that escapes it, because the
   `gebner_simple_effects` branch adds a new lattice axiom

       assume sub_effect GHOST ~> DIV            (ulib/FStar.Pervasives.fsti:196)

   which master does not have (master has only `PURE ~> DIV`, `DIV ~> EXN`, and
   `PURE ~> GHOST` in Prims).  A ghost value of an informative type therefore
   flows into extracted code, where it is compiled to `Obj.magic ()`.

   No `FStar.Ghost`, no `erased`, and no `assume val` is needed: any ordinary
   `GTot`/`Ghost` definition leaks.  And because of `DIV ~> EXN`,
   `DIV ~> STATE`, `EXN ~> ALL`, `STATE ~> ALL` and `DIV ~> TAC`, every ghost
   value also reaches `ML`, `ST`, `All` and `Tac`.

   Consequences observed on the branch:
     * `let pick (x: erased bool) : Dv int = if reveal x then 111 else 222`
       is verified to return 111 or 222, and returns 0.
     * `let getstr (x: erased string) : Dv string = reveal x` extracts to
       `let getstr (uu___ : unit) : Prims.string = (fun x -> Obj.magic ()) uu___`
       and the compiled program SEGFAULTS on `String.length`.

   The fix is to drop the `GHOST ~> DIV` edge; it is NOT a `solve_sub` problem
   (the branch's `edge` record carries no `mlift` at all any more).

   Every `expect_failure` below MUST be rejected.  This file verifies as-is on
   master.  When fixed, move to tests/micro-benchmarks/, and add a companion in
   tests/extraction/ asserting that no `Obj.magic` is emitted for an
   informative result type.
*)
module SimpleEffects_GhostLiftErasure

open FStar.Ghost

/// The smallest case: a plain `GTot` definition, no ghost library at all.
let g (x:int) : GTot int = x + 1

[@@ expect_failure]
let leak_gtot (x:int) : Dv int = g x

/// The `Ghost` (rather than `GTot`) node leaks too...
assume val g_ghost : unit -> Ghost bool (requires True) (ensures (fun _ -> True))

[@@ expect_failure]
let leak_ghost (u:unit) : Dv bool = g_ghost ()

/// ... via ascription and via bind.
assume val g_gtot : unit -> GTot bool

[@@ expect_failure]
let leak_ascription (u:unit) : Dv bool = g_gtot ()

[@@ expect_failure]
let leak_bind (u:unit) : Dv bool = let y = g_gtot () in y

/// Informative result type: extraction emits `Obj.magic ()` and the compiled
/// program dumps core on `String.length`.
[@@ expect_failure]
let getstr (x: erased string) : Dv string = reveal x

/// Verified to return 111 or 222; actually returns 0.
[@@ expect_failure]
let pick (x: erased bool) : Dv int = if reveal x then 111 else 222

/// `Dv` reaches `ML`, `ST`, `All` and `Tac` through the rest of the lattice.
[@@ expect_failure]
let leak_ml (x: erased bool) : FStar.All.ML bool = reveal x

/// --- Behaviour that MUST be preserved ---

/// The same coercion under `Tot` is correctly rejected today; keep it pinned so
/// the check is not lost.
[@@ expect_failure]
let tot_control (x: erased bool) : bool = reveal x

/// Non-informative result types stay erasable and must remain allowed.
let noninformative_is_fine (x: erased unit) : Dv unit = reveal x

/// The sound direction of the lattice: PURE may be used where Div is expected.
let pure_to_div (x:int) : Dv int = x + 1

(* NOTE: F* stops checking a module at the first error, so only the first
   `expect_failure` is reported as Error 303 on the branch.  Comment out the
   earlier cases to see each of the others succeed unsoundly as well. *)
