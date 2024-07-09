module Pulse.Class.Small

open Pulse.Lib.Pervasives

class small (v : slprop) = {
  pf : squash (is_slprop2 v);
}

instance val small_emp : small emp

instance val slprop2_star
  (p q : slprop)
  (sp : small p)
  (sq : small q) : small (p ** q)

instance val small_pure (p : prop) : small (pure p)

(* Intentionally not an instance. *)
val small_from_small_ref (v:slprop) (_ : squash (is_slprop2 v))
  : small v
