module Example.TestOnAutomation
#lang-pulse
open Pulse
open Pulse.Lib.Send

ghost
fn test_on_l_prover_emp (l:loc_id)
requires emp
ensures on l emp
{}

ghost
fn test_on_l_prover_pure (l:loc_id) (p:prop)
requires pure p
ensures on l (pure p)
{}

ghost
fn test_on_l_prover_star (l:loc_id) (p1 p2:slprop)
requires on l p1
requires on l p2
ensures on l (p1 ** p2)
{}

ghost
fn test_on_l_prover_exists (#a:Type0) (l:loc_id) (p1: a -> slprop)
requires exists* (x:a). on l (p1 x)
ensures on l (exists* (x:a). p1 x)
{}

ghost
fn test_on_l_prover_exists3 (#a:Type0) (l:loc_id) (p1: a -> a -> a -> slprop)
requires exists* (x y z:a). on l (p1 x y z)
ensures on l (exists* (x y z:a). p1 x y z)
{}

ghost
fn test_on_l_elim_emp (l:loc_id)
requires on l emp
ensures emp
{}

ghost
fn test_on_l_elim_pure (l:loc_id) (p:prop)
requires on l (pure p)
ensures pure p
{}

ghost
fn test_on_l_elim_star (l:loc_id) (p1 p2:slprop)
requires on l (p1 ** p2)
ensures on l p1
ensures on l p2
{}

ghost
fn test_on_l_elim_star2 (l:loc_id) (p1 p2:slprop)
requires on l (p1 ** p2)
ensures on l (p2 ** p1)
{}

ghost
fn test_on_l_elim_exists (#a:Type0) (l:loc_id) (p1: a -> slprop)
requires on l (exists* (x:a). p1 x)
ensures exists* (x:a). on l (p1 x)
{}

ghost
fn test_on_l_elim_exists3 (#a:Type0) (l:loc_id) (p1: a -> a -> a -> slprop)
requires  on l (exists* (x y z:a). p1 x y z)
ensures exists* (x y z:a). on l (p1 x y z)
{}

ghost
fn test_on_l_elim_exists3_star (#a:Type0) (l:loc_id) (p1 p2: a -> a -> a -> slprop)
requires  on l (exists* (x y z:a). p1 x y z ** p2 x y z)
ensures exists* (x y z:a). on l (p1 x y z) ** on l (p2 x y z)
{}

assume
val pred ([@@@mkey]x:int) (y:int) : slprop

ghost
fn test_pred_ext (l:loc_id) (r:int) (x y:int)
requires pred r (x + y)
ensures pred r (y + x)
{
  #set-options "--debug prover --print_implicits" { () }
}

ghost
fn test_pred_on_l_ext (l:loc_id) (r s:int) (x y:int)
requires on l (pred r (x + y))
ensures on l (pred r (y + x))
{}

[@@expect_failure]
ghost
fn test_pred_ext_key_failure (l:loc_id) (r s:int) (x y:int)
requires pred r (x + y)
requires pure (r == s)
ensures pred s (y + x)
{}

[@@expect_failure]
ghost
fn test_pred_on_l_ext_key_failure (l:loc_id) (r s:int) (x y:int)
requires on l (pred r (x + y))
requires pure (r == s)
ensures on l (pred s (y + x))
{}