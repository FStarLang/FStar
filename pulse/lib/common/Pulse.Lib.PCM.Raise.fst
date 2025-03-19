module Pulse.Lib.PCM.Raise
open FStar.PCM
open FStar.Ghost
module U = FStar.Universe

let raise (#a:Type u#a) (p:pcm a)
: pcm (U.raise_t u#a u#b a)
= let core : pcm' (U.raise_t u#a u#b a) = {
    composable = (fun x y -> composable p (U.downgrade_val x) (U.downgrade_val y));
    op = (fun x y -> U.raise_val (op p (U.downgrade_val x) (U.downgrade_val y)));
    one = U.raise_val p.p.one;
  } in
  let p : pcm (U.raise_t u#a u#b a) = { 
    p = core;
    comm = (fun x y -> p.comm (U.downgrade_val x) (U.downgrade_val y));
    assoc = (fun x y z -> p.assoc (U.downgrade_val x) (U.downgrade_val y) (U.downgrade_val z));
    assoc_r = (fun x y z -> p.assoc_r (U.downgrade_val x) (U.downgrade_val y) (U.downgrade_val z));
    is_unit = (fun x -> p.is_unit (U.downgrade_val x));
    refine = (fun x -> p.refine (U.downgrade_val x));
  } in
  p

let raise_compatible
    (#a:Type u#a) (p:pcm a) (x y:a)
: Lemma 
  (requires compatible p x y)
  (ensures compatible (raise u#a u#b p) (U.raise_val x) (U.raise_val y))
= eliminate exists frame.
      composable p x frame /\
      op p frame x == y
  returns compatible (raise u#a u#b p) (U.raise_val x) (U.raise_val y)
  with _ . (
    assert (composable (raise p) (U.raise_val x) (U.raise_val frame))
  )
 
    
let raise_refine
    (#a:Type u#a) (p:pcm a)
    (xa:FStar.Ghost.erased a)
    (f:(va:a{compatible p xa va}
        -> GTot (ya:a{compatible p ya va /\
                     frame_compatible p xa va ya})))
    (v:_ {compatible (raise u#a u#b p) (U.raise_val #a xa) v})
: GTot (y:_ { compatible (raise u#a u#b p) y v /\
              frame_compatible (raise p) (U.raise_val #a xa) v y /\
              y == U.raise_val (f (U.downgrade_val v))})
= let x = U.raise_val xa in
  let va = U.downgrade_val v in
  let ya = f va in
  let y = U.raise_val ya in
  assert (compatible p ya va);
  raise_compatible p ya va;
  y

  let raise_upd
      (#a:Type u#a) (#p:pcm a) (#x #y: erased a)
      (f:frame_preserving_upd p x y)
  : frame_preserving_upd (raise u#a u#b p) 
      (U.raise_val (reveal x)) (U.raise_val (reveal y))
  = fun x -> 
      let ra = f (U.downgrade_val x) in
      let res = U.raise_val ra in
      raise_compatible p y ra;
      res