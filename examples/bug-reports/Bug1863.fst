module Bug1863

[@expect_failure]
let f (x y z : nat) : Lemma true [SMTPat (x + y + z);
                                  SMTPatOr [[SMTPat x]; [SMTPat y]]] = ()
