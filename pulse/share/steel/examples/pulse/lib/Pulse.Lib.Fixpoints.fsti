module Pulse.Lib.Fixpoints

open Pulse.Lib.Core

val fix_1 (#a : Type) (#b : a -> Type)
  (ff : (x:a -> (y:a{y << x} -> Tot (b y)) -> Tot (b x)))
  : x:a -> Tot (b x)

val fix_ghost_1 (#a : Type0) (#b : a -> Type0)
  (ff : (x:a -> (y:a{y << x} -> GTot (b y)) -> GTot (b x)))
  : x:a -> GTot (b x)

val fix_stt_ghost_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (x:a -> (y:a{y << x} -> stt_ghost (b y) emp_inames (pre y) (post y)) -> stt_ghost (b x) emp_inames (pre x) (post x)))
  : x:a -> stt_ghost (b x) emp_inames (pre x) (post x)

val fix_stt_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (y:a -> stt (b y) (pre y) (post y)) -> (x:a -> stt (b x) (pre x) (post x)))
  : x:a -> stt (b x) (pre x) (post x)
