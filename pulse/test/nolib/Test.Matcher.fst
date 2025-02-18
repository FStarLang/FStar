module Test.Matcher
#lang-pulse

open Pulse.Nolib
open FStar.Tactics.V2

(* So the permissions show up in the output. *)
#set-options "--print_implicits"

(* Testing different matching modes. *)

(******* Default matching (d) *)
assume val dref (a : Type0) : Type0
assume val dpts_to
  (#a:Type0)
  ([@@@mkey] r:dref a)
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
  (#[exact (`1.0R)][@@@mkey]  p : perm)
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
