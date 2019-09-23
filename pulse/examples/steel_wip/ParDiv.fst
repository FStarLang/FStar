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
  | Par : pre0:_ -> #a0:_ -> post0:_ -> m0: m s c a0 pre0 post0 ->
          pre1:_ -> #a1:_ -> post1:_ -> m1: m s c a1 pre1 post1 ->
          #a:_ -> #post:_ -> k:(x0:a0 -> x1:a1 -> Dv (m s c a (c.star (post0 x0) (post1 x1)) post)) ->
          m s c a (c.star pre0 pre1) post


assume
val bools : nat -> bool

noeq
type step_result s (c:comm_monoid s) a (q:post a c) (frame:c.r) =
  | Step: p:_ -> m s c a p q -> state:s {c.interp (p `c.star` frame) state} -> nat -> step_result s c a q frame

let rec step #s #c (i:nat) #pre #a #post (f:m s c a pre post) (frame:c.r) (state:s)
  : Div (step_result s c a post frame)
        (requires
          c.interp (pre `c.star` frame) state)
        (ensures fun _ -> True)
  = match f with
    | Ret x ->
        Step (post x) (Ret x) state i

    | Act act1 k ->
        let b, state' = act1.sem state in
        assert (c.interp (pre `c.star` frame) state);
        act1.action_ok state frame;
        Step (act1.post b) (k b) state' i

    | Par pre0 post0 (Ret x0)
          pre1 post1 (Ret x1)
          k ->
        Step (post0 x0 `c.star` post1 x1) (k x0 x1) state i

    | Par pre0 post0 m0
          pre1 post1 m1
          k ->
        if bools i
        then let Step pre0' m0' state' j = step (i + 1) m0 (pre1 `c.star` frame) state in
             Step (pre0' `c.star` pre1) (Par pre0' post0 m0' pre1 post1 m1 k) state' j
        else let Step pre1' m1' state' j = step (i + 1) m1 (pre0 `c.star` frame) state in
             Step (pre0 `c.star` pre1') (Par pre0 post0 m0 pre1' post1 m1' k) state' j

let rec run #s #c (i:nat) #pre #a #post (f:m s c a pre post) (state:s)
  : Div (a & s)
    (requires
      c.interp pre state)
    (ensures fun (x, state') ->
      c.interp (post x) state')
  = match f with
    | Ret x -> x, state
    | _ ->
      let Step pre' f' state' j = step i f c.emp state in
      run j f' state'

let eff #s (#c:comm_monoid s) a (pre:c.r) (post: a -> c.r) =
  m s c a pre post

let return #s (#c:comm_monoid s) #a (x:a) (post:a -> c.r)
  : eff a (post x) post
  = Ret x

let rec bind #s (#c:comm_monoid s) #a #b (#p:c.r) (#q:a -> c.r) (#r:b -> c.r)
             (f:eff a p q)
             (g: (x:a -> eff b (q x) r))
  : Dv (eff b p r)
  = match f with
    | Ret x -> g x
    | Act act k ->
      Act act (fun x -> bind (k x) g)
    | Par pre0 post0 l
          pre1 post1 r
          k ->
      Par pre0 post0 l pre1 post1 r (fun x0 x1 -> bind (k x0 x1) g)

let par #s (#c:comm_monoid s)
        #a0 #p0 #q0 (m0:eff a0 p0 q0)
        #a1 #p1 #q1 (m1:eff a1 p1 q1)
 : eff (a0 & a1) (p0 `c.star` p1) (fun (x0, x1) -> q0 x0 `c.star` q1 x1)
 = Par p0 q0 m0
       p1 q1 m1
       #_ #(fun (x0, x1) -> c.star (q0 x0) (q1 x1)) (fun x0 x1 -> Ret (x0, x1))

(* Some dummy action instantiations, just for demonstration purposes.
   The specs are bogus, since the state and monoid etc. are fully generic here *)
let action_get s (c:comm_monoid s)
  : action c s
  = let sem s0 = s0, s0 in
    let pre = c.emp in
    let post _ = c.emp in
    {
      sem = sem;
      pre = pre;
      post = post;
      action_ok = fun _ _ -> ()
    }
let get #s (#c:comm_monoid s)
  : eff s c.emp (fun _ -> c.emp)
  = Act (action_get s c) Ret
