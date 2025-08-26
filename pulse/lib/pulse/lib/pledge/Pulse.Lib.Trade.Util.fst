module Pulse.Lib.Trade.Util
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module T = FStar.Tactics

ghost
fn refl
  (#[T.exact (`emp_inames)] is:inames)
  (p: slprop)
  ensures (trade #is p p)
{
  ghost fn aux () : trade_f #is p p =
  {
    ()
  };
  intro _ _ _ aux
}

ghost
fn refl'
  (#[T.exact (`emp_inames)] is:inames)
  (p q: slprop)
  requires pure (p == q)
  ensures (trade #is p q)
{
  refl #is p;
  rewrite (trade #is p p) as (trade #is p q)
}

ghost
fn curry
  (#is: inames)
  (p q r:slprop)
   requires trade #is (p ** q) r
   ensures trade #emp_inames p (trade #is q r)
{
    ghost fn aux () : trade_f p #(trade #is (p ** q) r) (trade #is q r) =
    { 
        ghost fn aux () : trade_f #is q #((trade #is (p ** q) r) ** p) r =
        { 
            elim _ _;
        };
        intro _ _ _ aux;
    };
    intro _ _ _ aux;
}

ghost
fn comm_l (#is: inames) (p q r:slprop)
   requires trade #is (p ** q) r
   ensures trade #is (q ** p) r
{
  slprop_equivs ();
  rewrite (trade #is (p ** q) r) as (trade #is (q ** p) r)
}

ghost
fn comm_r (#is: inames) (p q r:slprop)
   requires trade #is p (q ** r)
   ensures trade #is p (r ** q)
{
  slprop_equivs ();
  rewrite (trade #is p (q ** r)) as (trade #is p (r ** q))
}

ghost
fn assoc_hyp_l (#is: inames) (p q r s:slprop)
   requires trade #is (p ** (q ** r)) s
   ensures trade #is ((p ** q) ** r) s
{
  slprop_equivs ();
  rewrite (trade #is (p ** (q ** r)) s) as (trade #is ((p ** q) ** r) s)
}

ghost
fn assoc_hyp_r (#is: inames) (p q r s:slprop)
   requires trade #is ((p ** q) ** r) s
   ensures trade #is (p ** (q ** r)) s
{
  slprop_equivs ();
  rewrite (trade #is ((p ** q) ** r) s) as (trade #is (p ** (q ** r)) s)
}

ghost
fn assoc_concl_l (#is: inames) (p q r s:slprop)
   requires trade #is p ((q ** r) ** s)
   ensures trade #is p (q ** (r ** s))
{
  slprop_equivs ();
  rewrite (trade #is p ((q ** r) ** s)) as (trade #is p (q ** (r ** s)))
}

ghost
fn assoc_concl_r (#is: inames) (p q r s:slprop)
   requires trade #is p (q ** (r ** s))
   ensures trade #is p ((q ** r) ** s)
{
  slprop_equivs ();
  rewrite (trade #is p (q ** (r ** s))) as (trade #is p ((q ** r) ** s))
}

ghost
fn elim_hyp_l (#is: inames) (p q r:slprop)
    requires (trade #is (p ** q) r) ** p
    ensures (trade #is q r)
{
    curry _ _ _;
    elim _ _;
}

ghost
fn elim_hyp_r (#is: inames) (p q r:slprop)
    requires (trade #is (p ** q) r) ** q
    ensures (trade #is p r)
{
    comm_l _ _ _;
    curry _ _ _;
    elim _ _;
}

ghost
fn reg_l
  (#is : inames)
  (p p1 p2: slprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p ** p1) (p ** p2))
{
  ghost
  fn aux () : trade_f #is (p ** p1) #(trade #is p1 p2) (p ** p2) =
  {
    elim_trade #is p1 p2
  };
  intro _ _ _ aux
}

ghost
fn reg_r
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2)
  ensures (trade #is (p1 ** p) (p2 ** p))
{
  reg_l p p1 p2;
  slprop_equivs ();
  rewrite (trade #is (p ** p1) (p ** p2))
    as (trade #is (p1 ** p) (p2 ** p))
}

ghost
fn weak_concl_l
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p ** p2))
{
  ghost
  fn aux () : trade_f #is p1 #(trade #is p1 p2 ** p) (p ** p2) =
  {
    elim_trade #is p1 p2
  };
  intro _ _ _ aux
}

ghost
fn weak_concl_r
  (#is: inames)
  (p1 p2 p: slprop)
  requires (trade #is p1 p2) ** p
  ensures (trade #is p1 (p2 ** p))
{
  weak_concl_l p1 p2 p;
  slprop_equivs ();
  refl' #is (p ** p2) (p2 ** p);
  trade_compose p1 _ _
}

ghost
fn prod
  (#is: inames)
  (l1 r1 l2 r2: slprop)
  requires (trade #is l1 r1 ** trade #is l2 r2)
  ensures (trade #is (l1 ** l2) (r1 ** r2))
{
  ghost
  fn aux () : trade_f #is (l1 ** l2) #(trade #is l1 r1 ** trade #is l2 r2) (r1 ** r2) =
  {
    elim_trade #is l1 r1;
    elim_trade #is l2 r2
  };
  intro _ _ _ aux
}

ghost
fn rewrite_with_trade
  (#[T.exact (`emp_inames)] is:inames)
  (p1 p2: slprop)
  requires p1 ** pure (p1 == p2)
  ensures p2 ** (trade #is p2 p1)
{
  rewrite p1 as p2;
  ghost
  fn aux () : trade_f #is p2 p1 =
  {
    rewrite p2 as p1
  };
  intro_trade _ _ _ aux
}

ghost
fn trans_hyp_l
  (p1 p2 q r: slprop)
  requires
  trade p1 p2 **
  trade (p2 ** q) r
  ensures
  trade (p1 ** q) r
{
  refl q;
  prod p1 p2 q q;
  trans _ _ r
}

ghost
fn trans_hyp_r
  (p q1 q2 r: slprop)
  requires
  trade q1 q2 **
  trade (p ** q2) r
  ensures
  trade (p ** q1) r
{
  refl p;
  prod p p q1 q2;
  trans _ _ r
}

ghost
fn trans_concl_l
  (p q1 q2 r: slprop)
  requires
  trade p (q1 ** r) **
  trade q1 q2
  ensures
  trade p (q2 ** r)
{
  refl r;
  prod q1 q2 r r;
  trans p _ _
}

ghost
fn trans_concl_r
  (p q r1 r2: slprop)
  requires
  trade p (q ** r1) **
  trade r1 r2
  ensures
  trade p (q ** r2)
{
  refl q;
  prod q q r1 r2;
  trans p _ _
}
