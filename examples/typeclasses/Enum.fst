module Enum

open Easy
open FStar.Tactics.Typeclasses
open FStar.Tactics

type bound = option nat

let bounded_by (b:bound) n =
  match b with
  | Some b -> b2t (n <= b)
  | None -> True

let succ : bound -> bound = function | None -> None | Some b -> Some (b+1)

let bounded (b:bound) = n:nat{bounded_by b n}

class enum a = {
    max     : bound;
    toInt   : a -> bounded max;
    fromInt : bounded max -> a;
    inv1    : x:a -> Lemma (fromInt (toInt x) == x);
    inv2    : i:(bounded max) -> Lemma (toInt (fromInt i) == i);
}

instance enum_nat : enum nat =
  { max = None;
    toInt = id;
    fromInt = id;
    inv1 = easy;
    inv2 = easy;
  }

instance enum_opt (i:enum 'a): enum (option 'a) =
  { max = succ i.max;
    toInt = (function | None -> 0 | Some x -> 1 + i.toInt x);
    fromInt = (function | 0 -> None | x -> Some (i.fromInt (x-1)));
    inv1 = (function | None -> () | Some x -> i.inv1 x);
    inv2 = (function | 0 -> () | x -> i.inv2 (x-1));
  }
