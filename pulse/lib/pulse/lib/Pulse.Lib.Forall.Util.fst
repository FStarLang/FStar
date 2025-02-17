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

module Pulse.Lib.Forall.Util
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util
include Pulse.Lib.Forall
module I = Pulse.Lib.Stick.Util

let intro #a #p = Pulse.Lib.Forall.intro_forall #a #p
let elim #a #p = Pulse.Lib.Forall.elim_forall #a #p
 

ghost
fn trans_compose (#a #b #c:Type0) (p:a -> slprop) (q:b -> slprop) (r:c -> slprop)
                 (f: a -> GTot b) (g: b -> GTot c)
    requires (forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x))
    ensures forall* x. p x @==> r (g (f x))
{
    ghost fn aux (x:a)
        requires ((forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x)))
        ensures p x @==> r (g (f x))
    {
        ghost fn aux (_:unit) 
        requires ((forall* x. p x @==> q (f x)) ** (forall* x. q x @==> r (g x))) ** p x
        ensures r (g (f x))
        {
            elim #_ #(fun x -> p x @==> q (f x)) x;
            I.elim _ _;
            elim #_ #(fun x -> q x @==> r (g x)) (f x);
            I.elim _ _;
        };
        I.intro _ _ _ aux;
    };
    intro_forall _ aux
}



ghost
fn trans (#a:Type0) (p q r: a -> slprop)
    requires (forall* x. p x @==> q x) ** (forall* x. q x @==> r x)
    ensures forall* x. p x @==> r x
{
    admit(); /// GGG FIXME: rewrite under lambda
    trans_compose p q r id id;
}



ghost fn elim_forall_imp (#a:Type0) (p q: a -> slprop) (x:a)
    requires (forall* x. p x @==> q x) ** p x
    ensures q x
{
    elim #_ #(fun x -> p x @==> q x) x;
    I.elim _ _
}



ghost
fn intro_forall_imp (#a:Type0) (p q: a -> slprop) (r:slprop)
    (elim: (u:a -> stt_ghost unit
                        emp_inames
                        (r ** p u)
                        (fun _ -> q u)))
requires r
ensures forall* x. p x @==> q x
{
    ghost fn aux (x:a)
    requires r
    ensures p x @==> q x
    {
        ghost
        fn aux ()
        requires r ** p x 
        ensures q x
        {
            elim x;
        };
        I.intro _ _ _ aux;
    };
    intro _ aux
}

