module RangeStep

(* Checking that prims_to_fstar_range doesn't kill typing,
 * we previously got a "Patterns are incomplete" error. *)

assume new type proofstate

assume val set_proofstate_range : proofstate -> FStar.Range.range -> proofstate

noeq type result a =
    | Success of a * proofstate
    | Failed  of string * proofstate

let tac (a:Type) = proofstate -> M (result a)

let bind (a:Type) (b:Type) (r1 r2:range) (t1:tac a) (t2:a -> tac b) : tac b =
    fun ps ->
        let ps = set_proofstate_range ps (FStar.Range.prims_to_fstar_range r1) in
        let r = t1 ps in
        match r with
        | Success(a, ps')  ->
            t2 a ps'
        | Failed(msg, ps') -> Failed(msg, ps')
