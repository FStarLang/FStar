module Print.Test

open FStar.Tactics
open Print

let test_print_goal1 =
  assert_by_tactic (forall (y:int). y==0 ==> 0==y)
                    (fun () -> just_print "something")
