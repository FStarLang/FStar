module Pulse.Class.Small

open Pulse.Lib.Pervasives

instance small_emp : small emp = {
  pf = ();
}

instance small_star
  (p q : vprop)
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

let small_from_small_ref (v:vprop) (_ : squash (is_small v))
  : small v = {
  pf = ();
}
