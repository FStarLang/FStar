module Bug2352

assume val p : Type0
assume val q : Type0

let test_fails p q (f: unit -> squash p) (g:unit -> squash (p ==> q))
  : squash q
  = f (); g()

let test_ok p q (f: unit -> squash p) (g:unit -> squash (p ==> q))
  : squash q
  = let _ = f () in g()

let test_also_fails p q (f: unit -> squash p) (g:unit -> squash (p ==> q))
  : squash q
  = let _ : unit = f () in g()

let test_also_ok p q (f: unit -> Lemma p) (g:unit -> squash (p ==> q))
  : squash q
  = let _ : unit = f () in g()
