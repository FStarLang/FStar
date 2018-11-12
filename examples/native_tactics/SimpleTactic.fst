module SimpleTactic
open FStar.Tactics

[@ plugin]
let test () =
  dump "Test";
  print "hello";
  admit_all()
