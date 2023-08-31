module Pulse.Lib.Fixpoints

open Pulse.Lib.Core

let rec fix_1 (#a : Type) (#b : a -> Type)
  (ff : (x:a -> (y:a{y << x} -> Tot (b y)) -> Tot (b x)))
  : x:a -> Tot (b x)
  = fun x -> ff x (fix_1 ff)

let rec fix_ghost_1 (#a : Type0) (#b : a -> Type0)
  (ff : (x:a -> (y:a{y << x} -> GTot (b y)) -> GTot (b x)))
  : x:a -> GTot (b x)
  = fun x -> ff x (fix_ghost_1 ff)

let fix_stt_ghost_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (x:a -> (y:a{y << x} -> stt_ghost (b y) emp_inames (pre y) (post y)) -> stt_ghost (b x) emp_inames (pre x) (post x)))
  : x:a -> stt_ghost (b x) emp_inames (pre x) (post x)
  = fix_1 #a #(fun x -> stt_ghost (b x) emp_inames (pre x) (post x)) ff

friend Pulse.Lib.Core
open Steel.ST
open Steel.ST.Effect

(* No termination check needed by dropping into STT *)

let fix_stt_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (kk : ((y:a -> stt (b y) (pre y) (post y)) -> x:a -> stt (b x) (pre x) (post x)))
  : x:a -> stt (b x) (pre x) (post x)
  =
  let rec f (x:a) : STT (b x) (pre x) (post x) = 
    kk (fun y () -> f y) x ()
  in
  let ff (x:a) : stt (b x) (pre x) (post x) = fun () -> f x in
  ff
