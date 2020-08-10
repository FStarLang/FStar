module Steel.FramingDuplex.PCM

open FStar.PCM

open Steel.Channel.Protocol

let dprot' = protocol unit

module WF = FStar.WellFounded

// Simplifying protocols for now
let rec no_loop (p:dprot') = match p with
  | Return _ -> False
  | Msg _ a k -> (forall x. (WF.axiom1 k x; no_loop (k x)))
  | DoWhile _ _ -> False

let dprot = p:dprot'{no_loop p}

let is_send (p:dprot) = Msg? p && (Send? (Msg?._0 p))
let is_recv (p:dprot) = Msg? p && (Recv? (Msg?._0 p))

let empty_trace (p:dprot) : trace p p = Waiting p

noeq
type t (p:dprot) =
 | V : partial_trace_of p -> t p
 | A_W : q:dprot {is_send q} -> trace p q -> t p
 | A_R : q:dprot {is_recv q} -> trace p q -> t p
 | B_R : q:dprot {is_send q} -> trace p q -> t p
 | B_W : q:dprot {is_recv q} -> trace p q -> t p
 | Nil

let ahead (#p:dprot) (q q':dprot) (s:trace p q) (s':trace p q') : prop
  = squash ({ to = q'; tr = s'} `extended_to` { to = q; tr = s })

let rec trace_length #p #q (s:trace p q) : Tot nat (decreases s) = match s with
  | Waiting _ -> 0
  | Message _ _ _ t -> 1 + trace_length t

let composable #p : symrel (t p) = fun t0 t1 ->
    match t0, t1 with
    | _, Nil
    | Nil, _ -> True
    | A_W q s, B_R q' s'
    | B_R q' s', A_W q s -> ahead q q' s s'
    | B_W q s, A_R q' s'
    | A_R q' s', B_W q s -> ahead q q' s s'
    | A_R q s, B_R q' s'
    | B_R q' s', A_R q s -> ahead q q' s s' \/ ahead q' q s' s
    | _, _ -> False

let compose (#p:dprot) (s0:t p) (s1:t p{composable s0 s1}) =
  match s0, s1 with
  | a, Nil | Nil, a -> a
  | A_W q s, B_R q' s'
  | B_R q' s', A_W q s
  | B_W q s, A_R q' s'
  | A_R q' s', B_W q s -> V ({to = q; tr = s})
  | A_R q s, B_R q' s'
  | B_R q' s', A_R q s ->
      if trace_length s >= trace_length s' then V ({to = q; tr = s}) else V ({to = q'; tr = s' })

let p' (p:dprot) : pcm' (t p) = { composable = composable; op = compose; one = Nil }

let lemma_comm #p (x:t p) (y:t p{composable x y}) :
  Lemma (compose x y == compose y x)
  = ()

let lemma_assoc_l #p (x y:t p) (z:t p{composable y z /\ composable x (compose y z)})
  : Lemma (composable x y /\ composable (compose x y) z /\
           compose x (compose y z) == compose (compose x y) z)
  = ()

let lemma_assoc_r #p (x y:t p) (z:t p{composable x y /\ composable (compose x y) z})
  : Lemma (composable y z /\ composable x (compose y z) /\
           compose x (compose y z) == compose (compose x y) z)
  = ()

let lemma_is_unit #p (x:t p) : Lemma (composable x Nil /\ compose x Nil == x)
  = ()

let pcm (prot:dprot) : pcm (t prot) =
  { p = p' prot;
    comm = lemma_comm;
    assoc = lemma_assoc_l;
    assoc_r = lemma_assoc_r;
    is_unit = lemma_is_unit
}

open Steel.Memory
open Steel.FramingEffect
open FStar.Ghost

let chan (p:dprot) = ref (t p) (pcm p)

assume val pts_to (#p:dprot) (r:chan p) (v:(t p)) : slprop u#1

let endpoint_a (#p:dprot) (c:chan p) (next:dprot) (tr:trace p next) =
  pts_to c (if is_send next then A_W next tr else A_R next tr)

let endpoint_b (#p:dprot) (c:chan p) (next:dprot) (tr:trace p next) =
  pts_to c (if is_send next then B_R next tr else B_W next tr)

// From Basics

assume
val cond (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)

assume
val change_slprop
  (p q:slprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

assume val sl_admit (#a:Type) (p:slprop) (q:a -> slprop) : SteelT a p (fun x -> q x)


// From nik_fictional

let frame_compatible (#p:dprot) (x:t p) (v y:t p) =
  (forall (frame:t p). {:pattern (composable x frame)}
            composable x frame /\
            v == compose x frame ==>
            composable y frame /\
            v == compose y frame)

let refine #p (v:t p) = V? v \/ Nil? v


assume
val select_refine (#p:dprot)
                  (r:chan p)
                  (x:t p)
                  (f:(v:t p{compatible (pcm p) x v}
                      -> GTot (y:t p{compatible (pcm p) y v /\
                                  frame_compatible x v y})))
   : SteelT  (v:t p{compatible (pcm p) x v /\ refine v})
             (pts_to r x)
             (fun v -> pts_to r (f v))

// TODO: Use select refine to implement getters
// TODO: Only need A_R and B_R cases

assume
val write_a
  (#p:dprot)
  (r:chan p)
  (#next:dprot{more next /\ tag_of next = Send})
  (tr:trace p next)
  (x:msg_t next)
  :SteelT unit (pts_to r (A_W next tr)) (fun _ -> endpoint_a r (step next x) (extend tr x))


// assume
// val get (#p:dprot) (r:ref (t p) (pcm p)) (v0:erased (t p))
//   : SteelT (v:(t p){compatible (pcm p) v0 v}) (pts_to r v0) (fun v -> pts_to r v)

// assume
// val upd (r:ref stepper p) (v0:erased stepper) (v1:stepper { frame_preserving p v0 v1})
//   : SteelT unit (pts_to r v0) (fun _ -> pts_to r v1)

assume
val alloc (#p:dprot) (x:t p)
  : Steel (chan p) emp (fun r -> pts_to r x) (fun _ -> squash (compatible (pcm p) x x)) (fun _ _ _ -> True)


assume
val split (#p:dprot) (r:chan p) (v_full v0 v1:t p) (_:squash (composable v0 v1)) (_:squash (v_full == compose v0 v1))
  : SteelT unit (pts_to r v_full) (fun _ -> pts_to r v0 `star` pts_to r v1)


val new_chan (p:dprot)
  : SteelT (chan p) emp
           (fun c -> endpoint_a c p (empty_trace p) `star` endpoint_b c p (empty_trace p))

let lem #p (x:t p) : Lemma (requires V? x) (ensures compatible (pcm p) x x)
  = assert (composable x Nil);
    assert (compose Nil x == x)

let new_chan p =
  let v:t p = V ({to = p; tr = empty_trace p}) in
  lem v;
  let r = alloc v in
  split r v
    (if is_send p then A_W p (empty_trace p) else A_R p (empty_trace p))
    (if is_send p then B_R p (empty_trace p) else B_W p (empty_trace p))
    (admit()) ();
  r

val send_a (#p:dprot)
         (c:chan p)
         (#next:dprot{more next /\ tag_of next = Send})
         (x:msg_t next)
         (tr:trace p next)
    : SteelT unit
             (endpoint_a c next tr)
             (fun _ -> endpoint_a c (step next x) (extend tr x))

let send_a #p c #next x tr =
  change_slprop (endpoint_a c next tr) (pts_to c (A_W next tr)) (fun _ -> ());
  write_a c tr x
