module ParDiv

let associative #a (f: a -> a -> a) =
  forall x y z. f x (f y z) == f (f x y) z

let commutative #a (f: a -> a -> a) =
  forall x y. f x y == f y x

let is_unit #a (x:a) (f:a -> a -> a) =
  forall y. f x y == y /\ f y x == y

noeq
type comm_monoid (s:Type) = {
  r:Type;
  emp: r;
  star: r -> r -> r;
  interp: r -> s -> prop;
  laws: squash (associative star /\ commutative star /\ is_unit emp star)
}

noeq
type state = {
  s:Type;
  mon:comm_monoid s;
}

let post #s a (c:comm_monoid s) = a -> c.r

noeq
type action #s (c:comm_monoid s) (a:Type) = {
   sem: s -> (a * s);
   pre: c.r;
   post: a -> c.r;
   action_ok: (s0:s ->
              frame:c.r ->
              Lemma
                (c.interp (c.star pre frame) s0 ==>
                (let x, s1 = sem s0 in
                 c.interp (c.star (post x) frame) s1)))
}

noeq
type m (s:Type0) (c:comm_monoid s) : (a:Type0) -> c.r -> (post a c) -> Type =
  | Ret : #a:_ -> #post:(a -> c.r) -> x:a -> m s c a (post x) post
  | Act : #a:_ -> #post:(a -> c.r) -> #b:_ -> f:action c b -> k:(x:b -> Dv (m s c a (f.post x) post)) -> m s c a f.pre post
  | Par : pre0:_ -> post0:_ -> m0: m s c unit pre0 post0 ->
          pre1:_ -> post1:_ -> m1: m s c unit pre1 post1 ->
          m s c unit (c.star pre0 pre1) (fun _ -> c.star (post0 ()) (post1 ()))


// val run_one (s:_) (c:comm_monoid s) (a:_) (r0:_) (r1:_) (f: m s c a r0 r1) (s0:s)
//   : Div (a * s)
//     (requires c.interp r0 s0)
//     (ensures fun (x, s1) -> c.interp (r1 x) s1)

assume
val ax_run_left (s:_) (c:comm_monoid s)
             (a0:_) (p0:_) (q0:_) (f0: m s c a0 p0 q0)
             (a1:_) (p1:_) (q1:_) (f1: m s c a1 p1 q1)
             (state:s)
  : Div ((a0 & a1) & s)
    (requires
      c.interp (c.star p0 p1) state)
    (ensures fun ((x0, x1), state') ->
      c.interp (c.star (q0 x0) (q1 x1)) state')


// let rec run_one (s:Type0) (c:comm_monoid s) a r0 r1 (f: m s c a r0 r1) (state:s)
//   : Div (a * s)
//     (requires c.interp r0 state)
//     (ensures fun (x, state') -> c.interp (r1 x) state')
//   = match f with
//     | Ret x -> x, state
//     | Act f k ->
//       let b, state' = f.sem state in
//       f.action_ok state c.emp;
//       run_one s c a (f.post b) r1 (k b) state'
//     | Par a0 pre0 post0 m0 a1 pre1 post1 m1 ->
//       ax_run_left s c a0 pre0 post0 m0 a1 pre1 post1 m1 state

noeq
type thread s (c:comm_monoid s) =
  | Thread : p:c.r -> q:c.r -> m s c unit p (fun _ -> q) -> thread s c

let threads s c = list (thread s c)

let rec threads_pre #s #c (l:threads s c) : c.r =
  match l with
  | [] -> c.emp
  | hd::tl -> Thread?.p hd `c.star` threads_pre tl

let rec threads_post #s #c (l:threads s c) : c.r =
  match l with
  | [] -> c.emp
  | hd::tl -> Thread?.q hd `c.star` threads_post tl

assume
val pick_thread (#s:_) (#c:_) (i:nat) (l:threads s c{Cons? l})
  : thread s c & threads s c
  //pick the ith thread mod (length l)

assume
val pick_thread_pre (#s:_) (#c:_) (i:nat) (l:threads s c{Cons? l}) (state:s)
  : Lemma
    (requires (c.interp (threads_pre l) state))
    (ensures (
      let t, rest = pick_thread i l in
      c.interp (Thread?.p t `c.star` threads_pre rest) state))

assume
val pick_thread_post (#s:_) (#c:_) (i:nat) (l:threads s c{Cons? l}) (state:s)
  : Lemma
    (requires (
      let t, rest = pick_thread i l in
      c.interp (Thread?.q t `c.star` threads_post rest) state))
    (ensures (
      c.interp (threads_post l) state))

let rec run_threads #s #c (i:nat) (ts:threads s c) (state:s)
  : Div s
        (requires
          c.interp (threads_pre ts) state)
        (ensures fun state' ->
          c.interp (threads_post ts) state')
  = match ts with
    | [] -> state
    | _ ->
      let Thread p q m, rest = pick_thread i ts in
      pick_thread_pre i ts state;
      match m with
      | Ret x ->
        assert (c.interp (c.star p (threads_pre rest)) state);
        assume (c.interp (threads_pre rest) state);
        let state' = run_threads (i + 1) rest state in
        assert (c.interp (threads_post rest) state');
        assume (c.interp (c.star p (threads_post rest)) state');
        pick_thread_post i ts state';
        state'

      | Act act1 k ->
        let b, state' = act1.sem state in
        assert (c.interp (p `c.star` (threads_pre rest)) state);
        act1.action_ok state (threads_pre rest);
        assert (c.interp ((act1.post b) `c.star` threads_pre rest) state');
        let kthread = Thread (act1.post b) q (k b) in
        let threads = kthread :: rest in
        assert (threads_pre threads == ((act1.post b) `c.star` threads_pre rest));
        let state'' = run_threads (i + 1) threads state' in
        assert (c.interp (threads_post threads) state'');
        pick_thread_post i ts state'';
        state''

      | Par p0 q0 m0 p1 q1 m1 ->
        assert (p == p0 `c.star` p1);
        assume (q == (q0() `c.star` (q1())));
        assert (c.interp ((p0 `c.star` p1) `c.star` (threads_pre rest)) state);
        let t0 = Thread p0 (q0()) m0 in
        let t1 = Thread p1 (q1()) m1 in
        let threads = t0::t1::rest in
        assert (c.interp (threads_pre threads) state);
        let state'' = run_threads (i + 1) threads state in
        assert (c.interp (threads_post threads) state'');
        assert (c.interp (q0() `c.star` (q1() `c.star` threads_post rest)) state'');
        assert (c.interp ((q0() `c.star` q1()) `c.star` threads_post rest) state'');
        assert (c.interp (q `c.star` threads_post rest) state'');
        pick_thread_post i ts state'';
        assert (c.interp (threads_post ts) state'');
        state''




let rec run_right (s:_) (c:comm_monoid s)
                  (a0:_) (p0:_) (q0:_) (f0: m s c a0 p0 q0)
                  (a1:_) (p1:_) (q1:_) (f1: m s c a1 p1 q1)
                  (state:s)
  : Div ((a0 & a1) & s)
    (requires
      c.interp (c.star p0 p1) state)
    (ensures fun ((x0, x1), state') ->
      c.interp (c.star (q0 x0) (q1 x1)) state')
  = match f1 with
    | Ret x1 ->
      assert (c.interp (c.star p0 p1) state);
      assume (c.interp p0 state);
      let x0, state' = run_one s c a0 p0 q0 f0 state in
      assert (c.interp (q0 x0) state');
      assume (c.interp (c.star (q0 x0) (q1 x1)) state');
      (x0, x1), state'

    | Act act1 k ->
      let b, state' = act1.sem state in
      act1.action_ok state p0;
      ax_run_left s c a0 p0 q0 f0
                      a1 (act1.post b) q1 (k b) state'

    | Par a1_l p1_l q1_l f1_l
          a1_r p1_r q1_r f1_r ->







    | _ -> admit()

and run_left (s:Type0) (c:comm_monoid s)
             (a0:_) (p0:_) (q0:_) (f0: m s c a0 p0 q0)
             (a1:_) (p1:_) (q1:_) (f1: m s c a1 p1 q1)
             (state:s)
  : Div ((a0 & a1) & s)
    (requires
      c.interp (c.star p0 p1) state)
    (ensures fun ((x0, x1), state') ->
      c.interp (c.star (q0 x0) (q1 x1)) state')
  = match f0 with
    | Ret x0 ->
      let x1, state' = run_one s c a1 p1 q1 f1 state in
      (x0, x1), state'

    | _ -> admit()

  : Div ((a0 & a1) & s)
    (requires
      c.interp (c.star p0 p1) state)
    (ensures fun ((x0, x1), state') ->
      c.interp (c.star (q0 x0) (q1 x1)) state')



val run_one (s:_) (c:comm_monoid s)
            (a0:_) (p0:_) (q0:_) (f0: m s c a0 p0 q0)
  : Div (a & s)
    (requ



val run0 (c:comm_monoid s)
         a0 p0 q0 (f0: m s c a0 p0 q0)
         a1 p1 q1 (f1: m s c a1 p1 q1)
         (state:s)
  : Div ((a0 & a1) & s)
    (requires
      c.interp (c.star p0 p1) state)
    (ensures fun ((x0, x1), state') ->
      c.interp (c.star (q0 x0) (q1 x1)) state')
  = match f with
    | Ret x -> x, s0
    | Act f k ->
      let b, s1 = f.sem s0 in
      f.action_ok s0 c.emp;
      run s c a (f.post b) r1 (k b) s1
    | _ -> admit()

    Par pre0 post0 m0 pre1 post1 m1 ->
      run s c a r0 r1 f s0


  | Par : #a0:_ ->

  | Get : #a:_ -> pre:c.r -> post:post a c -> k:(s -> Dv (m s c a pre post)) -> m s c a pre post
  | Put : #a:_ -> pre:c.r -> post:post a c -> v:s -> k:(unit -> Dv (m s a pre post)) -> m s c a (fun _ -> pre v) post
  | Or  : #a0:_ -> #a1:_  -> pre0:pre s -> pre1:pre s -> post0:post a0 s -> post1:post a1 s ->
          c0:m s a0 pre0 post0 ->
          c1:m s a1 pre1 post1 ->
          m s (a0 & a1) (pre0 <*> pre1) (fun (x0, x1) s0 -> post0 x <*> post1 x1)





let pre s = s -> prop
let post a s = a -> s -> prop
let wp s a = post a s -> pre s

noeq
type m (s:Type0) : (a:Type0) -> pre s -> post a s -> Type =
  | Ret : #a:_ -> #post:post a s -> x:a -> m s a (post x) post
  | Get : #a:_ -> pre:pre s -> post:post a s -> k:(s -> Dv (m s a pre post)) -> m s a pre post
  | Put : #a:_ -> pre:pre s -> post:post a s -> v:s -> k:(unit -> Dv (m s a pre post)) -> m s a (fun _ -> pre v) post
  | Or : #a0:_ -> #a1:_  -> pre0:pre s -> pre1:pre s -> post0:post a0 s -> post1:post a1 s ->
          c0:m s a0 pre0 post0 ->
          c1:m s a1 pre1 post1 ->
          m s (a0 & a1) (pre0 <*> pre1) (fun (x0, x1) s0 -> post0 x <*> post1 x1)

let rec run s a pre post (c:m s a pre post) (v:s)
  : Div (a * s) (pre v) (fun (a, s) -> post a s)
  = match c with
    | Ret x -> x, v
    | Get _ _ k -> run s a pre post (k v) v
    | Put pre' _ v' k -> run s a pre' post (k ()) v'


  | MOr : #al:_ -> prel:_ -> postl:_ -> #ar:_ -> prer:_ -> postr:_ ->
          l:m s al prel postl ->
          r:m s ar prer postr ->
          m s (al & ar) (prel <*> prer) (postl <*> postr)

          #wpr:_ -> r:m s a wpr -> m s a (fun post s -> exists sl sr. sl <*> sr /\ wpl (fun sl' -> wpr

  // MOr instead of Or to avoid name clashes with FStar.Reflection
