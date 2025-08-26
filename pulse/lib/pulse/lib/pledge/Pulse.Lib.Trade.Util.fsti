module Pulse.Lib.Trade.Util
#lang-pulse
open Pulse.Lib.Pervasives
include Pulse.Lib.Trade

module T = FStar.Tactics

let intro
  (#[T.exact (`emp_inames)] is:inames)
= intro_trade #is

let elim
  (#is:inames)
= elim_trade #is

ghost
fn refl
  (#[T.exact (`emp_inames)] is:inames)
  (p: slprop)
  ensures (trade #is p p)

ghost
fn refl'
  (#[T.exact (`emp_inames)] is:inames)
  (p q: slprop)
  requires pure (p == q)
  ensures (trade #is p q)

ghost
fn curry
  (#is: inames)
  (p q r:slprop)
   requires trade #is (p ** q) r
   ensures trade #emp_inames p (trade #is q r)

let trans
  (#is : inames)
= trade_compose #is

ghost
fn comm_l (#is: inames) (p q r:slprop)
   requires trade #is (p ** q) r
   ensures trade #is (q ** p) r

ghost
fn comm_r (#is: inames) (p q r:slprop)
   requires trade #is p (q ** r)
   ensures trade #is p (r ** q)

ghost
fn assoc_hyp_l (#is: inames) (p q r s:slprop)
   requires trade #is (p ** (q ** r)) s
   ensures trade #is ((p ** q) ** r) s

ghost
fn assoc_hyp_r (#is: inames) (p q r s:slprop)
   requires trade #is ((p ** q) ** r) s
   ensures trade #is (p ** (q ** r)) s

ghost
fn assoc_concl_l (#is: inames) (p q r s:slprop)
   requires trade #is p ((q ** r) ** s)
   ensures trade #is p (q ** (r ** s))

ghost
fn assoc_concl_r (#is: inames) (p q r s:slprop)
   requires trade #is p (q ** (r ** s))
   ensures trade #is p ((q ** r) ** s)

ghost
fn elim_hyp_l (#is: inames) (p q r:slprop)
    requires (trade #is (p ** q) r) ** p
    ensures (trade #is q r)

ghost
fn elim_hyp_r (#is: inames) (p q r:slprop)
    requires (trade #is (p ** q) r) ** q
    ensures (trade #is p r)

ghost
fn reg_l
  (#is : inames)
  (p p1 p2: slprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p ** p1) (p ** p2))

ghost
fn reg_r
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p1 ** p) (p2 ** p))

ghost
fn weak_concl_l
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p ** p2))

ghost
fn weak_concl_r
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p2 ** p))

ghost
fn prod
  (#is: inames)
  (l1 r1 l2 r2: slprop)
  requires (trade #is l1 r1 ** trade #is l2 r2)
  ensures (trade #is (l1 ** l2) (r1 ** r2))

ghost
fn rewrite_with_trade
  (#[T.exact (`emp_inames)] is:inames)
  (p1 p2: slprop)
  requires p1 ** pure (p1 == p2)
  ensures p2 ** (trade #is p2 p1)

ghost
fn trans_hyp_l
  (p1 p2 q r: slprop)
  requires
  trade p1 p2 **
  trade (p2 ** q) r
  ensures
  trade (p1 ** q) r

ghost
fn trans_hyp_r
  (p q1 q2 r: slprop)
  requires
  trade q1 q2 **
  trade (p ** q2) r
  ensures
  trade (p ** q1) r

ghost
fn trans_concl_l
  (p q1 q2 r: slprop)
  requires
  trade p (q1 ** r) **
  trade q1 q2
  ensures
  trade p (q2 ** r)

ghost
fn trans_concl_r
  (p q r1 r2: slprop)
  requires
  trade p (q ** r1) **
  trade r1 r2
  ensures
  trade p (q ** r2)
