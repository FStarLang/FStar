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

module Pulse.Lib.Forall
open Pulse.Lib.Core

val ( forall* )
    (#a:Type u#a)
    (p:a -> vprop)
: vprop

val elim_forall
    (#a:Type)
    (#p:a->vprop)
    (x:a)
: stt_ghost unit emp_inames
    (forall* x. p x)
    (fun _ -> p x)

val intro_forall
    (#a:Type)
    (#p:a->vprop)
    (v:vprop)
    (f_elim : (x:a -> stt_ghost unit emp_inames v (fun _ -> p x)))
: stt_ghost unit emp_inames
    v
    (fun _ -> forall* x. p x)

val vprop_equiv_forall
    (#a:Type)
    (p q: a -> vprop)
    (_:squash (forall x. p x == q x))
: vprop_equiv (op_forall_Star p) (op_forall_Star q)
