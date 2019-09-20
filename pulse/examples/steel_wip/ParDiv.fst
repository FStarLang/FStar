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
  | Par : pre0:_ -> post0:_ -> m0: m s c unit pre0 (fun _ -> post0) ->
          pre1:_ -> post1:_ -> m1: m s c unit pre1 (fun _ -> post1) ->
          m s c unit (c.star pre0 pre1) (fun _ -> c.star post0 post1)

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
val pick_thread_pre (#s:_) (#c:_) (i:nat) (l:threads s c{Cons? l}) (state:s) (frame:c.r)
  : Lemma
    (requires (c.interp (threads_pre l `c.star` frame) state))
    (ensures (
      let t, rest = pick_thread i l in
      c.interp ((Thread?.p t `c.star` threads_pre rest) `c.star` frame) state))

assume
val pick_thread_post (#s:_) (#c:_) (i:nat) (l:threads s c{Cons? l}) (state:s) (frame:c.r)
  : Lemma
    (requires (
      let t, rest = pick_thread i l in
      c.interp ((Thread?.q t `c.star` threads_post rest) `c.star` frame) state))
    (ensures (
      c.interp (threads_post l `c.star` frame) state))

let elim_eq #a #b (f g : (a -> b)) (x:a)
  : Lemma (f == g ==> f x == g x)
  = ()

let rec run_threads #s #c (i:nat) (ts:threads s c) (state:s) (frame:c.r)
  : Div s
        (requires
          c.interp (threads_pre ts `c.star` frame) state)
        (ensures fun state' ->
          c.interp (threads_post ts `c.star` frame) state')
  = match ts with
    | [] -> state
    | _ ->
      let Thread p q m, rest = pick_thread i ts in
      pick_thread_pre i ts state frame;
      match m with
      | Ret x ->
        assert (c.interp ((p `c.star` (threads_pre rest)) `c.star` frame) state);
        let state' = run_threads (i + 1) rest state (p `c.star` frame) in
        assert (c.interp (threads_post rest `c.star` (p `c.star` frame)) state');
        pick_thread_post i ts state' frame;
        state'

      | Act act1 k ->
        let b, state' = act1.sem state in
        assert (c.interp (p `c.star` (threads_pre rest) `c.star` frame) state);
        act1.action_ok state (threads_pre rest `c.star` frame);
        let kthread = Thread (act1.post b) q (k b) in
        let threads = kthread :: rest in
        let state'' = run_threads (i + 1) threads state' frame in
        pick_thread_post i ts state'' frame;
        state''

      | Par p0 q0 m0 p1 q1 m1 ->
        assert (p == p0 `c.star` p1);
        elim_eq (fun () -> q) (fun () -> (q0 `c.star` q1)) ();
        assert (q == (q0 `c.star` q1));
        let t0 = Thread p0 q0 m0 in
        let t1 = Thread p1 q1 m1 in
        let threads = t0::t1::rest in
        let state'' = run_threads (i + 1) threads state frame in
        pick_thread_post i ts state'' frame;
        state''
