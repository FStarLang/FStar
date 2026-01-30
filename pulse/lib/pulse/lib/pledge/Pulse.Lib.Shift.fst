(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.Shift
#lang-pulse
open FStar.Ghost
open Pulse.Class.Duplicable
open Pulse.Lib.Pervasives


let shift_elim_t is hyp extra concl : Type u#5 =
  unit -> shift_f #is hyp #extra concl

let psquash (a:Type u#a) : prop = squash a

let shift_elim_exists (is:inames) (hyp extra concl:slprop) : slprop =
  pure (squash (shift_elim_t is hyp extra concl))

let extra_duplicable (p:slprop) = pure (squash (duplicable p))

let shift (#is:inames) (hyp concl:slprop) =
  exists* (extra:slprop). extra ** shift_elim_exists is hyp extra concl ** extra_duplicable extra

ghost
fn dup (p:slprop) (d:erased (duplicable p))
requires p
ensures p
ensures p
{
  let d = reveal d;
  dup p #d ()
}


ghost
fn intro_shift
  (#[T.exact (`emp_inames)] is:inames)
  (hyp concl:slprop)
  (extra:slprop)
  {| duplicable extra |}
  (f_elim: unit -> shift_f #is hyp #extra concl)
  requires extra
  ensures  shift #is hyp concl
{
  fold (shift_elim_exists is hyp extra concl);
  fold (extra_duplicable extra);
  fold (shift #is hyp concl)
}

fn introducable_shift_aux u#a (t: Type u#a) is is'
    hyp extra concl {| duplicable extra |} {| introducable is' (extra ** hyp) concl t |} (k: t) :
    stt_ghost unit is extra (fun _ -> shift #is' hyp concl) = {
  intro_shift #is' hyp concl extra fn _ {
    intro #is' concl #(extra ** hyp) (fun _ -> k);
  }
}

instance introducable_shift (t: Type u#a) is is'
    hyp extra concl {| duplicable extra |} {| introducable is' (extra ** hyp) concl t |} :
    introducable is extra (shift #is' hyp concl) t =
  { intro_aux = introducable_shift_aux t is is' hyp extra concl }


let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()



ghost
fn pextract (a:Type u#5) (pf:squash a)
returns i:a
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}

ghost
fn extract_eliminator (is:inames) (extra hyp concl: slprop)
requires shift_elim_exists is hyp (reveal extra) concl
returns i : shift_elim_t is hyp (reveal extra) concl
ensures shift_elim_exists is hyp (reveal extra) concl
{
  unfold (shift_elim_exists is hyp (reveal extra) concl);
  let pf : squash (psquash (shift_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (shift_elim_t is hyp (reveal extra) concl));
  let pf : squash (shift_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;
  let f = pextract (shift_elim_t is hyp (reveal extra) concl) pf;
  fold (shift_elim_exists is hyp (reveal extra) concl);
  f
}


ghost
fn extract_duplicator (extra:slprop)
requires extra_duplicable extra
returns d : duplicable extra
ensures extra_duplicable extra
{
  unfold (extra_duplicable extra);
  let pf : squash (psquash (duplicable extra)) =
    elim_pure_explicit (psquash (duplicable extra));
  let pf : squash (duplicable extra) =
    FStar.Squash.join_squash pf;
  let f = pextract (duplicable extra) ();
  fold (extra_duplicable extra);
  f
}

ghost
fn deconstruct_shift (is:inames) (hyp concl: slprop)
requires shift #is hyp concl
returns res:(extra:slprop &
             (duplicable extra &
              shift_elim_t is hyp extra concl))
ensures reveal (dfst res)
{
  unfold (shift #is hyp concl);
  with extra. assert (extra ** shift_elim_exists is hyp extra concl ** extra_duplicable extra);
  let d = extract_duplicator extra;
  let e = extract_eliminator is extra hyp concl;
  let res : (extra:slprop & (duplicable extra & shift_elim_t is hyp extra concl)) = (| extra, (d, e) |);
  rewrite (reveal extra) as (dfst res);
  drop_ (extra_duplicable extra);
  drop_ (shift_elim_exists is hyp extra concl);
  res
}

let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

ghost
fn elim_shift_alt
  (is:inames)
  (hyp concl:slprop)
requires shift #is hyp concl
requires hyp
ensures concl
opens is
{
  let res = deconstruct_shift is hyp concl;
  let f = dsnd res;
  rewrite (dfst res) as res._1;
  let g = snd f;
  call g()
}

let elim_shift #is = elim_shift_alt is

ghost
fn shift_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
requires shift #is1 hyp concl
ensures shift #is2 hyp concl
{
  let res = deconstruct_shift is1 hyp concl;

  let d = fst (dsnd res);
  let f = snd (dsnd res);

  intro (shift #is2 hyp concl) #(dfst res) fn _
  {
    rewrite (dfst res) as res._1;
    call f ()
  };
}

ghost
fn dup_extra_duplicable (extra:slprop)
requires extra_duplicable extra
ensures extra_duplicable extra
ensures extra_duplicable extra
{
  let d = extract_duplicator extra;
  fold (extra_duplicable extra);
}

ghost
fn dup_shift_elim_exists #is #extra hyp concl
requires shift_elim_exists is hyp extra concl
ensures shift_elim_exists is hyp extra concl
ensures shift_elim_exists is hyp extra concl
{
  let d = extract_eliminator _ _ _ _;
  fold (shift_elim_exists is hyp extra concl);
}

ghost
fn shift_dup #is p q : duplicable_f (shift #is p q) =
{
  unfold (shift #is p q);
  let d = extract_duplicator _;
  dup_extra_duplicable _;
  dup_shift_elim_exists _ _;
  Pulse.Class.Duplicable.dup _ #d ();
  fold (shift #is p q);
  fold (shift #is p q)
}

instance shift_duplicable
  (#is : inames)
  (p q : slprop)
: duplicable (shift #is p q)
= {
  dup_f = fun () -> shift_dup #is p q
}

ghost
fn shift_compose
  (#is : inames)
  (p q r : slprop)
requires shift #is p q
requires shift #is q r
ensures  shift #is p r
{
  intro (shift #is p r) #(shift #is p q ** shift #is q r) fn _
  {
    elim_shift #is p _;
    elim_shift #is _ _;
  };
}
