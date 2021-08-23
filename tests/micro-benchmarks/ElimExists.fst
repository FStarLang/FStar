module ElimExists
assume
val p (x y:nat) : Type0

assume
val trans (x y z:nat)
  : Lemma
    (requires p x y /\ p y z)
    (ensures p x z)


let test1 (x z:nat)
  : Lemma
    (requires
      (exists y. p x y /\ p y z))
    (ensures
      p x z)
  = _elim_exists_ y.
         p x y /\ p y z
    _to_ p x z
    _using_ _.
       trans x y z

assume
val trans_squash (#x #y #z:nat) (_:squash (p x y /\ p y z))
  : squash (p x z)

let test1_annot (x z:nat) (_:squash (exists y. p x y /\ p y z))
  : squash (p x z)
  = _elim_exists_ (y:nat).
         p x y /\ p y z
    _to_ p x z
    _using_ pf. (
       trans_squash pf
    )

let test2 (x z:nat)
  : Lemma
    (requires
      (exists y0 y1. p x y0 /\ p y0 y1 /\ p y1 z))
    (ensures
      p x z)
  = _elim_exists_ y0 y1.
       p x y0 /\ p y0 y1 /\ p y1 z
    _to_ p x z
    _using_  _. (
       trans y0 y1 z;
       trans x y0 z
    )
