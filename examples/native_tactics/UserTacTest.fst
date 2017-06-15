module UserTacTest

open FStar.Tactics
open UserPrintTactic

let test_print_goal1 =
  assert_by_tactic (user_print "something")
                   (forall (y:int). y==0 ==> 0==y)

let test2 =
  assert_by_tactic (just_prune)
                   (forall (y:int). y==0 ==> 0==y)