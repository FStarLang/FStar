module InameReduce

#lang-pulse
open Pulse.Nolib

[@@no_mkeys]
assume val foo : inames -> slprop

#push-options "--no_smt"
fn test1 ()
  requires foo []
  ensures  foo emp_inames
{ (); }

fn test2 ()
  requires foo emp_inames
  ensures  foo []
{ (); }
#pop-options

fn test3 (is : list iname)
  requires foo is ** pure (Nil? is)
  ensures  foo emp_inames
{ (); }

fn test4 (is : list iname)
  requires foo is ** pure (Nil? is)
  ensures  foo []
{ (); }
