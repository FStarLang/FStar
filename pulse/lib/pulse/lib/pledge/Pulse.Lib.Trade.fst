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

module Pulse.Lib.Trade
#lang-pulse

open Pulse.Lib.Pervasives


let trade_elim_t is hyp extra concl : Type u#5 =
  unit -> trade_f #is hyp #extra concl

let trade_elim_exists (is:inames) (hyp extra concl:slprop) : slprop =
  pure (squash (trade_elim_t is hyp extra concl))

let trade (#is:inames) (hyp concl:slprop) =
  exists* extra. extra ** trade_elim_exists is hyp extra concl


ghost
fn intro_trade
  (#[T.exact (`emp_inames)]is:inames)
  (hyp concl extra:slprop)
  (f_elim: unit -> trade_f #is hyp #extra concl)
  requires extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  assert (extra ** trade_elim_exists is hyp extra concl);
  fold (trade #is hyp concl)
}

fn introducable_trade_aux u#a (t: Type u#a) is is'
    hyp extra concl {| introducable is' (extra ** hyp) concl t |} (k: t) :
    stt_ghost unit is extra (fun _ -> trade #is' hyp concl) = {
  intro_trade #is' hyp concl extra fn _ {
    intro #is' concl #(extra ** hyp) (fun _ -> k);
  }
}

instance introducable_trade (t: Type u#a) is is'
    hyp extra concl {| introducable is' (extra ** hyp) concl t |} :
    introducable is extra (trade #is' hyp concl) t =
  { intro_aux = introducable_trade_aux t is is' hyp extra concl }

instance introducable_trade' (t: Type u#a) is
    hyp extra concl {| introducable emp_inames (extra ** hyp) concl t |} :
    introducable is extra (hyp @==> concl) t =
  { intro_aux = introducable_trade_aux t is emp_inames hyp extra concl }

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

ghost
fn pextract (a:Type u#5) (_:squash a)
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
fn deconstruct_trade (is:inames) (hyp concl: slprop)
  requires trade #is hyp concl
  returns res:(extra:erased slprop & trade_elim_t is hyp (reveal extra) concl)
  ensures reveal (dfst res)
{
  unfold (trade #is hyp concl);
  with extra. assert (extra ** trade_elim_exists is hyp extra concl);
  unfold (trade_elim_exists is hyp (reveal extra) concl);
  let pf : squash (psquash (trade_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (trade_elim_t is hyp (reveal extra) concl));
  let pf : squash (trade_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;
  let f = pextract (trade_elim_t is hyp (reveal extra) concl) pf;
  let res =
    (| (extra <: erased slprop), f |) <: (p:erased slprop & trade_elim_t is hyp (reveal p) concl);
  rewrite (reveal extra) as (reveal (dfst res));
  res
}

let call #t #is #req #ens (h: unit -> stt_ghost is t req (fun x -> ens x)) = h

ghost
fn elim_trade
  (#[T.exact (`emp_inames)]is:inames)
  (hyp concl:slprop)
  requires trade #is hyp concl ** hyp
  ensures concl
  opens is
{
  let res = deconstruct_trade is hyp concl;
  let f = dsnd res;
  rewrite dfst res as res._1;
  call f ()
}

ghost
fn trade_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
  requires trade #is1 hyp concl
  ensures trade #is2 hyp concl
{
  let res = deconstruct_trade is1 hyp concl;

  intro (trade #is2 hyp concl) #(dfst res) fn _ {
    let f = dsnd res;
    rewrite dfst res as res._1;
    call f ()
  };
}


ghost
fn trade_map
  (#is : inames)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
  requires trade #is p q
  ensures  trade #is p r
{
  intro (trade #is p r) #(trade #is p q) fn _
  {
    elim_trade #is _ _;
    f ();
  };
}


ghost
fn trade_compose
  (#is : inames)
  (p q r : slprop)
  requires trade #is p q ** trade #is q r
  ensures  trade #is p r
{
  intro (trade #is p r) #(trade #is p q ** trade #is q r) fn _
  {
    elim_trade #is p _;
    elim_trade #is _ _;
  };
}

ghost
fn eq_as_trade
  (p1 p2 : slprop)
  requires pure (p1 == p2)
  ensures  p2 @==> p1
{
  intro (p2 @==> p1) fn _{ rewrite p2 as p1 }
}

ghost
fn rewrite_with_trade
  (p1 p2 : slprop)
  requires p1 ** pure (p1 == p2)
  ensures  p2 ** (p2 @==> p1)
{
  eq_as_trade p1 p2;
  rewrite p1 as p2;
  ();
}

ghost
fn is_send_across_trade #b #g #is
  (p1 p2: slprop) {| i1: is_send_across #b g p1, i2: is_send_across g p2 |}
  : is_send_across g (trade #is p1 p2) = l1 l2 {
  ghost_impersonate l2 (on l1 (trade #is p1 p2)) (on l2 (trade #is p1 p2)) fn _ {
    loc_dup l2;
    intro (trade #is p1 p2) #(on l1 (trade #is p1 p2) ** loc l2) fn _ {
      on_intro p1;
      i1 l2 l1;
      ghost_impersonate #is l1 (on l1 p1 ** on l1 (trade #is p1 p2)) (on l1 p2) fn _ {
        on_elim p1;
        on_elim (trade #is p1 p2);
        elim_trade #is _ _;
        on_intro p2
      };
      i2 l1 l2;
      on_elim p2;
      drop_ (loc l2);
    };
    on_intro (trade #is p1 p2);
  };
}
