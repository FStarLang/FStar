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
   pre: c.r;
   post: a -> c.r;
   sem: (frame:c.r -> s0:s{c.interp (c.star pre frame) s0} -> (x:a & s1:s{c.interp (post x `c.star` frame) s1}));
}

noeq
type m (s:Type u#1) (c:comm_monoid s) : (a:Type u#a) -> c.r -> (post a c) -> Type =
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
        let (| b, state' |) = act1.sem frame state in
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

(* Some dummy instantiations, just for demonstration purposes. *)
assume val heap : Type u#1
assume val hm : comm_monoid heap
assume val hm_affine (r0 r1:hm.r) (h:heap)
  : Lemma (hm.interp (r0 `hm.star` r1) h ==>
           hm.interp r0 h)
assume val ref : Type u#0 -> Type u#0
assume val ptr_live (r:ref 'a) : hm.r
assume val pts_to (r:ref 'a) (x:'a) : hm.r
assume val sel (x:ref 'a) (h:heap{hm.interp (ptr_live x) h})
  : Tot 'a
assume val sel_ok (x:ref 'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
           (hm_affine (ptr_live x) frame h;
            let v = sel x h in
            hm.interp (pts_to x v `hm.star` frame) h))
assume val upd (x:ref 'a) (v:'a) (h:heap{hm.interp (ptr_live x) h})
  : Tot heap
assume val upd_ok (x:ref 'a) (v:'a) (h:heap) (frame:hm.r)
  : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
           (hm_affine (ptr_live x) frame h;
            let h' = upd x v h in
            hm.interp (pts_to x v `hm.star` frame) h'))

let (!) (x:ref 'a)
  : eff 'a (ptr_live x) (fun v -> pts_to x v)
  = let act : action hm 'a =
    {
      pre = ptr_live x;
      post = pts_to x;
      sem = (fun frame h0 ->
        hm_affine (ptr_live x) frame h0;
        sel_ok x h0 frame;
        (| sel x h0, h0 |))
    } in
    Act act Ret

let (:=) (x:ref 'a) (v:'a)
  : eff unit (ptr_live x) (fun _ -> pts_to x v)
  = let act : action hm unit =
    {
      pre = ptr_live x;
      post = (fun _ -> pts_to x v);
      sem = (fun frame h0 ->
        hm_affine (ptr_live x) frame h0;
        upd_ok x v h0 frame;
        (| (), upd x v h0 |))
    } in
    Act act Ret
