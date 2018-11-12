module Bug125

open FStar.Mul

val test: a:int -> Lemma (* ( requires (True) ) *)
                         (ensures ( a * a >= 0 ))
                         [SMTPat ( a * a ) ]
let test a = ()
