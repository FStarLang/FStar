module JoinLinkFactOrder
#lang-pulse
open Pulse.Lib.Pervasives

(* A branch leaves the state at a record built from a fresh existential [c],
   and the record is only well-typed because of a pure fact the branch knows
   about [c]: its field is refined to be positive. Joining with the (empty)
   "else" branch, where the state is a variable, generalizes the whole record
   over a fresh binder. The link recording what that binder stands for in the
   "then" branch must state the fact before the equation whose typing depends
   on it. Without the link, the postcondition's [y.k == k] is lost. *)

noeq type box = { k: bool; v: (x:int { x > 0 }) }

assume val cell : int -> slprop
assume val holds : box -> slprop

assume val unwrap (_:unit) (#x:erased box)
: stt_ghost unit emp_inames (holds x) (fun _ -> cell x.v)

assume val wrap (k:bool) (#c:erased (x:int { x > 0 }))
: stt_ghost unit emp_inames (cell c) (fun _ -> holds ({ k = k; v = reveal c }))

assume val step (_:unit) (#v:erased int)
: stt unit (cell v) (fun _ -> exists* (c:int). cell c ** pure (c > 0))

fn step_if (b k:bool) (#x:erased box)
requires holds x ** pure (x.k == k)
ensures exists* y. holds y ** pure (y.k == k)
{
  if b { unwrap (); step (); wrap k } else { () };
  ()
}
