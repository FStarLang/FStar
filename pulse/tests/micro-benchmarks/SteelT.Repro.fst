module SteelT.Repro
open Steel.Memory.Tactics
open Steel.Memory
open SteelT.Effect
//open Steel.Effect

assume
val myref : Type0

assume
val myref_slprop (x:myref) : slprop

assume
val dependent_provides (_:unit)
  : SteelT myref emp myref_slprop

assume
val nop (_:unit) : SteelT unit emp (fun c -> emp)

assume
val h_admit (#a:Type) (#[@@resolve_framing] p:slprop) (q:a -> slprop) : SteelT a p q

assume
val my_frame_t
  (outer:slprop)
  (#[@@resolve_framing] frame:slprop)
  (#[@@resolve_framing] _:squash (can_be_split_into outer emp frame))
  (_:unit)
  : SteelT unit outer (fun _ -> frame)

open FStar.Tactics
module T = FStar.Tactics

inline_for_extraction noextract let resolve_frame () : Tac unit =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_only [`%can_be_split_into]];
  norm [delta_attr [`%__reduce__];
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  canon()

[@@resolve_implicits; resolve_framing]
let resolve () : Tac unit =
    let n = T.ngoals() in
    if n = 21 then T.fail "Correct number of goals: Not solving any implicits"
    else T.admit_all()


//#push-options "--debug Repro --debug_level ResolveImplicitsHook"
#push-options "--print_implicits"
val test_ok1 (_:unit)
  : SteelT unit emp (fun c -> emp)
[@@expect_failure [189]]
// FIXME: 189 and 287 appeared during reshuffle in layered effects
//        used to be only 228
// GM: 287 no longer an F* error
let test_ok1 _
  = let tr = dependent_provides () in
    let c = my_frame_t (myref_slprop tr) (*#(myref_slprop tr)*) () in
    h_admit #unit (*(myref_slprop tr)*) (fun _ -> emp)
