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

module Pulse.Lib.Pervasives
#lang-pulse
include Pulse.Main
include Pulse.Lib.Core
include Pulse.Lib.Inv
include Pulse.Lib.Send
include Pulse.Lib.Forall
include Pulse.Lib.Array
include Pulse.Lib.Reference
include Pulse.Lib.Reference.Array
include Pulse.Lib.Primitives // TODO: what if we want to support several architectures?
include Pulse.Class.PtsTo
include Pulse.Class.Duplicable
include Pulse.Class.Introducable { intro }
include Pulse.Lib.SmallType { small_type }
include PulseCore.FractionalPermission
include PulseCore.Observability
include FStar.Ghost

module GSet = FStar.GhostSet

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val perform
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : stt a pre post
let perform f = f ()

val perform_ghost
  (#a #opens_ #pre #post : _)
  (f : unit -> stt_ghost a opens_ pre post)
  : stt_ghost a opens_ pre post
let perform_ghost f = f ()

(* TEMPORARY! REMOVE! *)
let inames_ext (is1 is2 : inames)
  : Lemma (requires forall i. GSet.mem i is1 <==> GSet.mem i is2)
          (ensures is1 == is2)
          [SMTPat (is1 == is2)]
  = GSet.lemma_equal_intro is1 is2

let inames_join_emp_r (is1 : inames)
  : Lemma (join_inames is1 emp_inames == is1) [SMTPat (join_inames is1 emp_inames)]
  = GSet.lemma_equal_intro (join_inames is1 emp_inames) is1

let inames_join_emp_l (is1 : inames)
  : Lemma (join_inames emp_inames is1 == is1) [SMTPat (join_inames emp_inames is1)]
  = GSet.lemma_equal_intro (join_inames emp_inames is1) is1

let inames_join_self (is1 : inames)
  : Lemma (join_inames is1 is1 == is1) [SMTPat (join_inames is1 is1)]
  = GSet.lemma_equal_intro (join_inames is1 is1) is1

//
// Native extraction in the Rust backend
//

fn ref_apply u#a u#b (#a: Type u#a) (#b:Type u#b) (r:ref (a -> b)) (x:a) (#f:erased (a -> b))
  requires pts_to r f
  returns y:b
  ensures pts_to r f ** pure (y == (reveal f) x)
{
  let f = !r;
  f x
}


//
// Native extraction in the Rust backend
//
let tfst (x:'a & 'b & 'c) : 'a = Mktuple3?._1 x
let tsnd (x:'a & 'b & 'c) : 'b = Mktuple3?._2 x
let tthd (x:'a & 'b & 'c) : 'c = Mktuple3?._3 x

// some convenience functions
module T = FStar.Tactics
let default_arg (t:T.term) = T.exact t


ghost
fn call_ghost 
      (#a:Type0)
      (#b: a -> Type0)
      (#pre: a -> slprop)
      (#post: (x:a -> b x -> slprop))
      (f:(x:a -> stt_ghost (b x) emp_inames (pre x) (fun y -> post x y)))
      (x:a)
  requires pre x
  returns y:erased (b x)
  ensures post x y
{
  let y = f x;
  rewrite (post x y) as (post x (reveal (hide y)));
  hide y
}



ghost
fn elim_cond_true (b:bool) (p q:slprop)
  requires (cond b p q ** pure (b == true))
  ensures p
{
  rewrite (cond b p q) as p;
}  



ghost
fn elim_cond_false b p q
  requires (cond b p q ** pure (b == false))
  ensures q
{
  rewrite (cond b p q) as q;
}  



ghost
fn intro_cond_true (p q:slprop)
  requires p
  ensures cond true p q
{
  fold (cond true p q);
}



ghost
fn intro_cond_false (p q:slprop)
  requires q
  ensures cond false p q
{
  fold (cond false p q);
}

type rust_extraction_attr =
  | Rust_const_fn
  | Rust_generics_bounds : list string -> rust_extraction_attr
  | Rust_derive : string -> rust_extraction_attr
  | Rust_mut_binder


ghost
fn dup_star (p q:slprop) {| duplicable p |} {| duplicable q |} : duplicable_f (p ** q) =
{
  open Pulse.Class.Duplicable;
  dup p ();
  dup q ()
}

instance duplicable_star (p q : slprop)  {| duplicable p |}  {| duplicable q|} : duplicable (p ** q) = {
  dup_f = (fun _ -> dup_star p q)
}

instance duplicable_slprop_ref_pts_to x y : duplicable (slprop_ref_pts_to x y) = {
  dup_f = (fun _ -> slprop_ref_share x #y)
}

ghost fn dup_emp () : duplicable_f emp = { }
instance duplicable_emp : duplicable emp = { dup_f = dup_emp }
