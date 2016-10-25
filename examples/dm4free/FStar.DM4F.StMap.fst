module FStar.DM4F.StMap

open FStar.DM4F.ST
open FStar.Map

type t (a:Type) (b : a -> Type0) : Type = x:a -> Tot (b x)
type t0 (a:eqtype) (b:Type) = Map.t a b

total new_effect_for_free STMAP = STATE_h (t0 int int)
