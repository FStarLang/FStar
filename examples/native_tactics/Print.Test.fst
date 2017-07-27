module Print.Test

open FStar.Tactics
open Print

let test_print_goal1 =
  assert_by_tactic (just_print "something")
                   (forall (y:int). y==0 ==> 0==y)
