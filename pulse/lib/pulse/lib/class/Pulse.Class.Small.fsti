module Pulse.Class.Small

open Pulse.Lib.Pervasives

class small (v : vprop) = {
  pf : squash (is_small v);
}

instance val small_emp : small emp

instance val small_star
  (p q : vprop)
  (sp : small p)
  (sq : small q) : small (p ** q)

instance val small_pure (p : prop) : small (pure p)

(* Intentionally not an instance. *)
val small_from_small_ref (v:vprop) (_ : squash (is_small v))
  : small v
