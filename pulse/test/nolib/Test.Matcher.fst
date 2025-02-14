module Test.Matcher
#lang-pulse

open Pulse.Nolib
open FStar.Tactics.V2

#set-options "--print_implicits"

(* Testing different matching modes. *)

(******* Default matching (d) *)
assume val dref (a : Type0) : Type0
assume val dpts_to
  (#a:Type0)
  (r:dref a)
  (#[exact (`1.0R)] p : perm)
  (v : erased a)
  : slprop


fn d_basic_self (r:dref int)
  requires dpts_to r 1
  ensures  dpts_to r 1
{ (); }



fn d_basic_id (r:dref int)
  requires dpts_to (id r) 1
  ensures  dpts_to r 1
{ (); }



fn d_basic_perm_comm (r:dref int) (p:perm)
  requires dpts_to r #(p +. 0.1R) 1
  ensures  dpts_to r #(0.1R +. p) 1
{ (); }


(******* Fast matching on the permission. *)
assume val fref (a : Type0) : Type0
assume val fpts_to
  (#a:Type0)
  (r:fref a)
  (#[exact (`1.0R)][@@@equate_strict]  p : perm)
  (v : erased a)
  : slprop


fn f_basic_self (r:fref int)
  requires fpts_to r 1
  ensures  fpts_to r 1
{ (); }



fn f_basic_id (r:fref int)
  requires fpts_to (id r) 1
  ensures  fpts_to r 1
{ (); }


[@@expect_failure] // fastunif will not commute nor generate guards

fn f_basic_perm_comm (r:fref int) (p:perm)
  requires fpts_to r #(p +. 0.1R) 1
  ensures  fpts_to r #(0.1R +. p) 1
{ (); }



(******* Syntactic matchin on the permission. *)
(* What's a concrete difference with _strict, since both sides
are already in normal form? *)
assume val sref (a : Type0) : Type0
assume val spts_to
  (#a:Type0)
  (r:sref a)
  (#[exact (`1.0R)][@@@equate_syntactic]  p : perm)
  (v : erased a)
  : slprop


fn s_basic_self (r:sref int)
  requires spts_to r 1
  ensures  spts_to r 1
{ (); }



fn s_basic_id (r:sref int)
  requires spts_to (id r) 1
  ensures  spts_to r 1
{ (); }


[@@expect_failure] // fastunif will not commute nor generate guards

fn s_basic_perm_comm (r:sref int) (p:perm)
  requires spts_to r #(p +. 0.1R) 1
  ensures  spts_to r #(p +. 0.10R) 1
{ (); }

