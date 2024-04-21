module Fundeps

[@@Tactics.Typeclasses.fundeps [0]]
class setlike (e:Type) (s:Type) = {
  empty : s;
  add : e -> s -> s;
  remove : e -> s -> s;
  contains : e -> s -> bool;
  size : s -> int;
}

assume val set (a:Type) : Type

assume
instance val setlike_set (a:Type) : setlike a (set a)

let test (s : set int) = size s
