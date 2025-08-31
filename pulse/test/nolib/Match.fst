module Match

#lang-pulse
open Pulse.Nolib

type t1 = | A | B
type t2 =
  | C : x:int -> y:int{x > y} -> t2
  | D

assume val foo : int -> slprop

let rel (x: t1) (y: t2) : slprop =
  match x, y with
  | A, C _ _ -> foo 1
  | B, D -> foo 2
  | _ -> pure False

let rel_cases_pred (x:t1) (y:t2) : bool =
  match x, y with
  | A, C _ _ -> true
  | B, D -> true
  | _ -> false

ghost
fn rel_cases (x:t1) (y:t2)
  requires rel x y
  ensures  rel x y ** pure (rel_cases_pred x y)
{
  if (rel_cases_pred x y) {
    ()
  } else {
    rewrite rel x y as pure False;
    unreachable ();
  }
}

fn test (x : t1) (y z : t2)
  requires rel x y ** rel x z
  ensures rel x y ** rel x z ** pure (C? y == C? z)
{
  rel_cases x y;
  rel_cases x z;
  match x {
    A -> {
      let C y1 y2 = y;
      let C z1 z2 = z;
      rewrite each C z1 z2 as z;
      rewrite each C y1 y2 as y;
      rewrite each A as x;
      ()
    }
    B -> {
      norewrite let D = y;
      norewrite let D = z;
      rewrite each B as x;
    }
  }
}

fn isC (x : t2)
  returns bool
{
  match x {
    C .. -> { true }
    D -> { false }
  }
}
