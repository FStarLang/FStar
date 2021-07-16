module Steel.C.PCM

unfold
let one (#a: Type) (p: pcm a) = p.p.one

let pcm (a: Type) : Tot Type =
  (p: FStar.PCM.pcm a {
    (forall (x:a) (y:a{composable p x y}).{:pattern (composable p x y)}
      op p x y == one p ==> x == one p /\ y == one p) /\ // necessary to lift frame-preserving updates to unions
    (forall (x:a) . {:pattern (p.refine x)} p.refine x ==> exclusive p x) /\ // nice to have, but not used yet
    (~ (p.refine (one p))) // necessary to maintain (refine ==> exclusive) for uninit
  })
