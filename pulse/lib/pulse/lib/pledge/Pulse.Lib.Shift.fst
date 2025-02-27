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


let shift_elim_t is hyp extra concl : Type u#4 =
  unit -> stt_ghost unit is (extra ** hyp) (fun _ -> concl)

let psquash (a:Type u#a) : prop = squash a

let shift_elim_exists (is:inames) (hyp extra concl:slprop) : slprop =
  pure (squash (shift_elim_t is hyp extra concl))

let extra_duplicable (p:slprop) = pure (squash (duplicable p))

let shift (#is:inames) (hyp concl:slprop) =
  exists* (extra:slprop). extra ** shift_elim_exists is hyp extra concl ** extra_duplicable extra

ghost
fn dup (p:slprop) (d:erased (duplicable p))
requires p
ensures p ** p
{
  let d = reveal d;
  dup p #d ()
}


ghost
fn intro_shift_alt
  (#is:inames)
  (hyp concl:slprop)
  (extra:slprop)
  {| d: duplicable extra |}
  (f_elim: unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
requires extra
ensures shift #is hyp concl
{
  fold (shift_elim_exists is hyp extra concl);
  fold (extra_duplicable extra);
  fold (shift #is hyp concl)
}

let intro_shift #is = intro_shift_alt #is


let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()



ghost
fn pextract (a:Type u#4) (pf:squash a)
requires emp
returns i:a
ensures emp
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

ghost
fn elim_shift_alt
  (is:inames)
  (hyp concl:slprop)
requires shift #is hyp concl ** hyp
ensures concl
opens is
{
  let res = deconstruct_shift is hyp concl;
  let f = dsnd res;
  rewrite (dfst res) as res._1;
  let g = snd f;
  g()
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

  ghost
  fn aux ()
    requires (dfst res ** hyp)
    ensures concl
    opens is2
  {
    rewrite (dfst res) as res._1;
    f ()
  };

  intro_shift #is2 hyp concl (dfst res) #d aux

}

ghost
fn dup_extra_duplicable (extra:slprop)
requires extra_duplicable extra
ensures extra_duplicable extra ** extra_duplicable extra
{
  let d = extract_duplicator extra;
  fold (extra_duplicable extra);
}

ghost
fn dup_shift_elim_exists #is #extra hyp concl
requires shift_elim_exists is hyp extra concl
ensures shift_elim_exists is hyp extra concl ** shift_elim_exists is hyp extra concl
{
  let d = extract_eliminator _ _ _ _;
  fold (shift_elim_exists is hyp extra concl);
}

ghost
fn shift_dup #is p q
requires shift #is p q
ensures shift #is p q ** shift #is p q
{
  unfold (shift #is p q);
  dup_extra_duplicable _;
  dup_shift_elim_exists _ _;
  let d = extract_duplicator _;
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
fn dup_star (p q:slprop) {| duplicable p |} {| duplicable q |}
requires p ** q
ensures (p ** q) ** (p ** q)
{
  open Pulse.Class.Duplicable;
  dup p ();
  dup q ()
}

instance duplicable_star (p q : slprop)  {| duplicable p |}  {| duplicable q|} : duplicable (p ** q) = {
  dup_f = (fun _ -> dup_star p q)
}

ghost
fn shift_compose
  (#is : inames)
  (p q r : slprop)
requires shift #is p q ** shift #is q r
ensures  shift #is p r
{
  ghost
  fn aux ()
    requires (shift #is p q ** shift #is q r) ** p
    ensures r
    opens is
  {
    elim_shift #is p _;
    elim_shift #is _ _;
  };
  intro_shift #is p r (shift #is p q ** shift #is q r) aux;

}
