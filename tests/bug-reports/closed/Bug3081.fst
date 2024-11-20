module Bug3081

// Fail if we warn about missing a variable in an SMTPat
#set-options "--warn_error @271"

assume val t: Type0

class toto = {
  f: t -> t -> t;
  g: t -> t -> t;
  f_lemma: x:t -> y:t -> squash (f x y == g y x);
}

// Lemma that can be proven using f_lemma twice
val test_lemma:
  {|toto|} ->
  x:t -> y:t -> z:t ->
  Lemma
  (f x (f y z) == g (g z y) x)

// It can't be proven automatically
[@@expect_failure]
let test_lemma #toto_instance x y z = ()

val f_lemma_smtpat:
  {|toto|} ->
  x:t -> y:t ->
  Lemma (f x y == g y x)
  [SMTPat (f x y)]
  // ^ This pattern mentions the dictionary after tc resolution
  // so we shouldn't warn.
let f_lemma_smtpat #toto_instance x y =
  f_lemma x y

// The SMT pattern works well
let test_lemma #toto_instance x y z = ()
