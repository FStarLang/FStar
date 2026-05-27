module Bug387
#lang-pulse

open Pulse.Nolib

type st t = | A | B of t

let tag #t (x : st t) : slprop = emp

ghost
fn is_tree_case_none (t:Type0) (l:st t)
  requires tag l
{
  drop_ (tag l);
  ();
}
 
fn rec height (t:Type0) (l : st t)
  requires tag l
{
  is_tree_case_none _ _;
}
