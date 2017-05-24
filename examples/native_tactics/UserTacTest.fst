module UserTacTest

open FStar.Tactics
open UserPrintTactic

let test_print_goal =
  assert_by_tactic (user_print "something")
                   (forall (y:int). y==0 ==> 0==y)