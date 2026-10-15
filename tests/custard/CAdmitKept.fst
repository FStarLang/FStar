module CAdmitKept

(* FStarLang/FStar#4661.  [admit] is a placeholder, not a proof: nothing
   says control cannot reach it, so the branch that leads to it must survive
   and abort when taken.  It used to be pruned like Pulse's [unreachable],
   and [kept] compiled to an unconditional [return 0].

   [pruned] is the control: there the dead branch's [false_elim] is justified
   by the refinement on [b], so it is genuinely unreachable and is still
   dropped. *)

let kept (b: bool) : FStar.UInt32.t =
  if b then 0ul else admit ()

let pruned (b: bool{b}) : FStar.UInt32.t =
  if b then 0ul else FStar.Pervasives.false_elim ()

let main () : FStar.UInt32.t =
  FStar.UInt32.add_mod (kept true) (pruned true)
