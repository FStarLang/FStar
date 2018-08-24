module Bug1521

type path = | L of path | O

private noeq type heap = {
  pos : path;
}

let prefix (p1 p2 : path) = False

let prefix_trans (p1 p2 p3 : path) : Lemma (requires (prefix p1 p2 /\ prefix p2 p3))
                                           (ensures (prefix p1 p3))
                                           [ SMTPat (prefix p1 p2); SMTPat (prefix p2 p3) ] = ()

let heap_rel (h1:heap) (h2:heap) = prefix h1.pos h2.pos

let rtest0 (h1 h2 h3 : heap) (_ : (heap_rel h1 h2 /\ heap_rel h2 h3)) =
  assert (heap_rel h1 h3)

let rtest1 (h1 h2 h3 : heap) (_ : squash (heap_rel h1 h2)) (_ : squash (heap_rel h2 h3)) =
  assert (heap_rel h1 h3)

let rtest2 (h1 h2 h3 : heap) (_ : (heap_rel h1 h2)) (_ : heap_rel h2 h3) =
  assert (heap_rel h1 h3)

let rtest2' (h1 h2 h3 : heap) (_ : (heap_rel h1 h2)) (_ : heap_rel h2 h3) =
  assert (heap_rel h1 h2);
  assert (heap_rel h1 h3)

let rtest2'' (h1 h2 h3 : heap) (_ : (heap_rel h1 h2)) (_ : heap_rel h2 h3) =
  assert (heap_rel h2 h3);
  assert (heap_rel h1 h3)

let ptest1 (p1 p2 p3 : path) (_ : squash (prefix p1 p2)) (_ : squash (prefix p2 p3)) =
  assert (prefix p1 p3)

let ptest2 (p1 p2 p3 : path) (_ : (prefix p1 p2)) (_ : (prefix p2 p3)) =
  assert (prefix p1 p3)

let sklem0 #a (#p : a -> prop) (_ : squash ((x:a & p x))) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

let sklem1 #a (#p : a -> prop) (_ : (exists (x:a). p x)) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

let sklem2 #a (#p : a -> prop) (_ : (u:unit{(exists (x:a). p x)})) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

[@expect_failure]
let sklem3 #a (#p : a -> prop) (_ : squash (exists (x:a). p x)) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()

let id (a:Type) = a
let sklem3' #a (#p : a -> prop) (_ : squash (exists (x:a). id (p x))) (phi:prop) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi) = ()
