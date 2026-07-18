module Bug1863

[@@expect_failure [326]]
let f (x y z : nat) : Lemma True [SMTPat (x + y + z);
                                  SMTPatOr [[SMTPat x]; [SMTPat y]]] = ()
