module Bug2352

assume val p : Type0
assume val q : Type0

let test_fails p q (f: unit -> p) (g:unit -> (p ==> q))
  : q
  = f (); g()

let test_ok p q (f: unit -> p) (g:unit -> (p ==> q))
  : q
  = let _ = f () in g()

let test_also_fails p q (f: unit -> p) (g:unit -> (p ==> q))
  : q
  = let _ : unit = f () in g()

let test_also_ok p q (f: unit -> Lemma p) (g:unit -> (p ==> q))
  : q
  = let _ : unit = f () in g()
