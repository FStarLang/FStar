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

val fix_1 (#a : Type) (#b : a -> Type)
  (ff : (x:a -> (y:a{y << x} -> Tot (b y)) -> Tot (b x)))
  : x:a -> Tot (b x)

val fix_ghost_1 (#a : Type0) (#b : a -> Type0)
  (ff : (x:a -> (y:a{y << x} -> GTot (b y)) -> GTot (b x)))
  : x:a -> GTot (b x)

val fix_stt_ghost_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (x:a -> (y:a{y << x} -> stt_ghost (b y) (pre y) (post y)) -> stt_ghost (b x) (pre x) (post x)))
  : x:a -> stt_ghost (b x) (pre x) (post x)

val fix_stt_1 (#a : Type) (#b : a -> Type) (#pre : a -> vprop) (#post : (x:a -> b x -> vprop))
  (ff : (y:a -> stt (b y) (pre y) (post y)) -> (x:a -> stt (b x) (pre x) (post x)))
  : x:a -> stt (b x) (pre x) (post x)
