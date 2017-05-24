module Arith
unfold let op_Star = Prims.op_Multiply

#reset-options "--z3cliopt smt.arith.nl=false --smtencoding.elim_box true --smtencoding.nl_arith_repr native --smtencoding.l_arith_repr native"
irreducible
let test1 (a:nat) = assert ((3 * (3 * a)) / 3 == a * 3)

irreducible
let test2 (a:nat) = assert (((3 * 3) * a) / 3 == a * 3)

irreducible
let test3 (t:nat) (a:nat) = assert (t=3 ==> (t * (t * a)) / t == a * t)

irreducible
let test4 (t:nat) (a:nat) = assert (t=3 ==> ((t * t) * a) / t == a * t)

irreducible
let test5 (a:nat) (b:nat) = assert (a * b == b * a)

irreducible
let test6 (a:nat) (b:nat) (c:nat) = assert (a * (b * c) == (a * b) * c)

irreducible
let test7 (a:nat) (b:nat) (c:nat) = assert (a * (b + c) == (a * b) + (a * c))

irreducible
let test8 (a:nat) (b:nat) (c:nat) = assert (a * (b + c) == (c * a) + (a * b))

irreducible
let test9 (f:nat -> nat) (a:nat) (b:nat) (c:nat) = assert (f a * (b + c) == (c * f a) + (f a * b))

#set-options "--smtencoding.nl_arith_repr wrapped"
irreducible
let test10 (a:nat) (b:nat) (c:nat) (z:nat) = assert (a==z ==> a * (b + c) == (c * a) + (z * b))

#set-options "--smtencoding.nl_arith_repr native"
irreducible
let test11 (a:nat) (b:nat) (c:nat) (d:nat) (e:nat) =
  assert ((a + b + c + d + e) * (a + b + c + d + e) == (a * a) 
                                                    + 2 * (a * b) 
                                                    + 2 * (a * c) 
                                                    + 2 * (a * d)                                      
                                                    + 2 * (a * e) 
                                                    + (b * b)
                                                    + 2 * (b * c) 
                                                    + 2 * (b * d)  
                                                    + 2 * (b * e)
                                                    + (c * c)
                                                    + 2 * (c * d)  
                                                    + 2 * (c * e) 
                                                    + (d * d)
                                                    + 2 * (d * e) 
                                                    + (e * e))
