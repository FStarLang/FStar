module Pulse.Class.Small

open Pulse.Lib.Pervasives

instance small_emp : small emp = {
  pf = ();
}

instance slprop2_star
  (p q : slprop)
  (sp : small p)
  (sq : small q)
  : small (p ** q) = {
  pf = ();
}

instance small_pure
  (p : prop)
  : small (pure p) = {
  pf = ();
}

let small_from_small_ref (v:slprop) (_ : squash (is_slprop2 v))
  : small v = {
  pf = ();
}
