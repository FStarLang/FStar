module Repro
open Steel.Memory.Tactics
open Steel.Memory
//open SteelT.Effect
open Steel.Effect

assume
val myref : Type0

assume
val myref_hprop (x:myref) : hprop

assume
val dependent_provides (_:unit)
  : SteelT myref emp myref_hprop

assume
val nop (_:unit) : SteelT unit emp (fun c -> emp)

assume
val h_admit (#a:Type) (#p:hprop) (q:a -> hprop) : SteelT a p q

assume
val my_frame_t
  (outer:hprop)
  (#[resolve_frame()]
    frame:hprop{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer emp frame /\ True)}
  )
  (_:unit)
  : SteelT unit outer (fun _ -> frame)

val test_fails2 (_:unit)
  : SteelT unit emp (fun c -> emp)

//succeeds if you open SteelT.Effect instead of Steel.Effect
let test_fails2 _
  = let tr = dependent_provides () in
    let c = my_frame_t (myref_hprop tr) (*#(myref_hprop tr)*) () in
    h_admit #unit #_(*(myref_hprop tr)*) (fun _ -> emp)
