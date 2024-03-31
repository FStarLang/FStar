(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

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

(* No termination check needed by dropping into STT *)

let fix_stt_1_div
    (#a : Type)
    (#b : a -> Type)
    (#pre : a -> vprop)
    (#post : (x:a -> b x -> vprop))
    (kk : ((y:a -> unit -> Dv (stt (b y) (pre y) (post y))) ->
            x:a -> unit -> Dv (stt (b x) (pre x) (post x))))
: x:a -> unit -> Dv (stt (b x) (pre x) (post x))
=  let rec f (x:a) (_:unit) : Dv (stt (b x) (pre x) (post x)) = 
      kk (fun y () -> f y ()) x ()
   in
   f

let fix_stt_1
    (#a : Type)
    (#b : a -> Type)
    (#pre : a -> vprop)
    (#post : (x:a -> b x -> vprop))
    (kk : ((y:a -> stt (b y) (pre y) (post y)) -> x:a -> stt (b x) (pre x) (post x)))
: x:a -> stt (b x) (pre x) (post x)
= fun x -> 
    hide_div (fix_stt_1_div #a #b #pre #post (fun f x () -> kk (fun y -> hide_div (f y)) x) x)
      