module Basic

[@(expect_failure [189])]
let _  = 1 + true

[@(expect_failure [19])] let _ =     assert False
[@(expect_failure [19])] let _ = (); assert False
[@(expect_failure [19])] let _ =     assert False; ()
[@(expect_failure [19])] let _ = (); assert False; ()

[@(expect_failure [19])] let _ =     assert_norm False
[@(expect_failure [19])] let _ = (); assert_norm False
[@(expect_failure [19])] let _ =     assert_norm False; ()
[@(expect_failure [19])] let _ = (); assert_norm False; ()

[@(expect_failure [19])]
let test2 () : Lemma false = ()

[@(expect_failure [19])]
let test3 () : Lemma False = ()

[@(expect_failure [19])]
let test6 () : Lemma (normalize_term False) = ()
