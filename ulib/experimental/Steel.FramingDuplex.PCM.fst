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
  = ({ to = q'; tr = s'} `extended_to` { to = q; tr = s }) /\ True

let ahead_refl (#p:dprot) (q:dprot) (s:trace p q)
  : Lemma (ahead q q s s)
  = ()

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
val cond (#a:Type) (b:bool) (p: (b':bool{b == b'}) -> slprop) (q: bool -> a -> slprop)
         (then_: (squash (b == true) -> SteelT a (p true) (q true)))
         (else_: (squash (b == false) -> SteelT a (p false) (q false)))
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

let rec is_trace_prefix
  (#from:protocol unit) (#to #to':protocol unit)
  (tr:trace from to)
  (tr':trace from to')
  : Tot prop
    (decreases tr)
  = match tr with
    | Waiting _ -> True
    | Message _ x _ tail ->
      match tr' with
      | Waiting _ -> False
      | Message _ x' _ tail' -> x == x' /\ is_trace_prefix tail tail'

let rec lemma_is_trace_prefix_refl
  (#from #to:protocol unit)
  (tr:trace from to)
  : Lemma (ensures is_trace_prefix tr tr)
          (decreases tr)
  = match tr with
    | Waiting _ -> ()
    | Message _ _ _ tail -> lemma_is_trace_prefix_refl tail

let rec lemma_is_trace_prefix_extend (#from #to #to':protocol unit)
  (tr:trace from to)
  (tr':trace from to')
  (x:msg_t to')
  : Lemma (requires is_trace_prefix tr tr' /\ more_msgs to')
          (ensures is_trace_prefix tr (extend tr' x))
          (decreases tr)
  = match tr with
    | Waiting _ -> ()
    | Message _ msg _ tail ->
      match tr' with
      | Message from' msg' to' tail' -> lemma_is_trace_prefix_extend tail tail' x

let lemma_ahead_msg_msg_inversion
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to')
  : Lemma (requires Message? tr /\ Message? tr' /\ is_trace_prefix tr tr')
          (ensures Message?.x tr == Message?.x tr' /\ is_trace_prefix (Message?._3 tr) (Message?._3 tr'))
  = let Message _ x _ tail = tr in
    let Message _ x' _ tail' = tr' in
    let l = ({to = to; tr = tr}) in
    let r = ({to = to'; tr = tr'}) in
    let open FStar.ReflexiveTransitiveClosure in
    let stable1 (z:partial_trace_of from) : Type0 = Message? z.tr /\ Message?.x z.tr == x in
    let aux1 (y z:partial_trace_of from)
      : Lemma (requires stable1 y /\ next y z)
              (ensures stable1 z)
      = ()
    in Classical.forall_intro_2 (Classical.move_requires_2 aux1);
    stable_on_closure next stable1 ();
    assert (x == x');
    let stable2 (z:partial_trace_of (step from x)) : Type0 =
      is_trace_prefix tail z.tr
    in
    let aux2 (y z:partial_trace_of (step from x))
      : Lemma (requires stable2 y /\ next y z)
              (ensures stable2 z)
      = Classical.forall_intro (Classical.move_requires (lemma_is_trace_prefix_extend tail y.tr))
    in Classical.forall_intro_2 (Classical.move_requires_2 aux2);
    stable_on_closure next stable2 ()

let rec next_message_aux
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to'{trace_length tr' > trace_length tr /\ is_trace_prefix tr tr'})
  : Tot (msg_t to)
        (decreases tr)
  = match tr with
    | Waiting _ ->
        assert (Message? tr');
        Message?.x tr'
    | Message _ x to tail ->
      let Message _ x' to' tail' = tr' in
      lemma_ahead_msg_msg_inversion tr tr';
      next_message_aux tail tail'

let lemma_ahead_implies_trace_prefix
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to')
  : Lemma (requires ahead to' to tr' tr)
          (ensures is_trace_prefix tr tr')
  = let stable (z:partial_trace_of from) : Type0 = is_trace_prefix tr z.tr in
    let aux (y z:partial_trace_of from)
      : Lemma (requires stable y /\ next y z)
              (ensures stable z)
      = Classical.forall_intro (Classical.move_requires (lemma_is_trace_prefix_extend tr y.tr))
   in Classical.forall_intro_2 (Classical.move_requires_2 aux);
   let open FStar.ReflexiveTransitiveClosure in
   stable_on_closure next stable ();
   lemma_is_trace_prefix_refl tr

let next_message
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to'{trace_length tr' > trace_length tr /\
    ahead to' to tr' tr})
  = lemma_ahead_implies_trace_prefix tr tr';
    next_message_aux tr tr'

let rec extend_increase_length (#from #to:protocol unit) (t:trace from to{more_msgs to}) (m:next_msg_t to)
  : Lemma (ensures trace_length (extend t m) == trace_length t + 1)
          (decreases t)
  = match t with
    | Waiting _ -> ()
    | Message _ _ _ tail -> extend_increase_length tail m

let next_increase_length (#p:dprot) (x y:partial_trace_of p)
  : Lemma (requires next x y)
          (ensures trace_length y.tr == trace_length x.tr + 1)
  = let aux (msg:next_msg_t x.to)
        : Lemma (requires y.to == step x.to msg /\ y.tr == extend x.tr msg)
                (ensures trace_length y.tr == trace_length x.tr + 1)
        = extend_increase_length x.tr msg
    in Classical.forall_intro (Classical.move_requires aux)

let rec lemma_ahead_is_longer (#p:dprot) (q:dprot) (s:trace p q) (q':dprot) (s':trace p q')
  : Lemma (requires ahead q q' s s')
          (ensures trace_length s >= trace_length s')
  = let open FStar.ReflexiveTransitiveClosure in
    let l = ({to = q'; tr = s'}) in
    let r = ({to = q; tr = s}) in
    let stable_p (x:partial_trace_of p) : Type0 = trace_length x.tr >= trace_length s' in
    let aux (x y:partial_trace_of p)
      : Lemma (requires stable_p x /\ next x y)
              (ensures stable_p y)
      = next_increase_length x y
    in Classical.forall_intro_2 (fun x -> Classical.move_requires (aux x));
    stable_on_closure next stable_p ()

let compatible_a_r_v_is_ahead
  (#p:dprot) (#q:dprot{is_recv q}) (tr:trace p q)
  (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (A_R q tr) (V tr'))
          (ensures ahead tr'.to q tr'.tr tr)
  =  let aux (frame:t p) : Lemma
        (requires composable (A_R q tr) frame /\ compose frame (A_R q tr) == V tr')
        (ensures ahead tr'.to q tr'.tr tr)
        = assert (B_R? frame \/ B_W? frame);
          if B_W? frame then ()
          else
            let q' = B_R?.q frame in
            let tr' = B_R?._1 frame in
            if trace_length tr' >= trace_length tr then
              Classical.move_requires (lemma_ahead_is_longer q tr q') tr'
            else ahead_refl q tr
    in
    Classical.forall_intro (Classical.move_requires aux)

  let extend_node_a_r (#p:dprot) (#q:dprot{more q /\ is_recv q}) (tr:trace p q)
  (tr':partial_trace_of p{trace_length tr'.tr > trace_length tr /\
    compatible (pcm p) (A_R q tr) (V tr')})
  : (y:t p)
  = compatible_a_r_v_is_ahead tr tr';
    let x = next_message tr tr'.tr in
    let q' = step q x in
    let tr' = extend tr x in
    if is_send q' then A_W q' tr' else A_R q' tr'

let lemma_compatible_a_greater_length (#p:dprot) (q:dprot{is_recv q}) (tr:trace p q) (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (A_R q tr) (V tr'))
          (ensures trace_length tr'.tr >= trace_length tr)
  = compatible_a_r_v_is_ahead tr tr';
    lemma_ahead_is_longer tr'.to tr'.tr q tr

let lemma_next_injectivity
  (#p:dprot) (tr tr':partial_trace_of p)
  (z1 z2:partial_trace_of p)
  : Lemma (requires tr `extended_to` tr' /\
            (next tr z1 /\ z1 `extended_to` tr') /\
            (next tr z2 /\ z2 `extended_to` tr'))
          (ensures z1 == z2)
  = admit()

let frame_compatible_a_extend (#p:dprot)
  (q:dprot{is_recv q /\ more q}) (tr:trace p q)
  (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (A_R q tr) (V tr') /\ trace_length tr'.tr > trace_length tr)
          (ensures frame_compatible (A_R q tr) (V tr') (extend_node_a_r tr tr'))
  = let x = A_R q tr in
    let p_tr:partial_trace_of p = {to = q; tr = tr} in
    let v = V tr' in
    let y = extend_node_a_r tr tr' in
    let aux (frame:t p)
      : Lemma (requires composable x frame /\ v == compose x frame)
              (ensures composable y frame /\ v == compose y frame)
      = assert (B_R? frame \/ B_W? frame);
        if B_W? frame then (
          let q_w = B_W?.q frame in
          let tr_w = B_W?._1 frame in
          assert (tr_w == tr'.tr);
          // TODO: Likely need to strengthen the pcm
          // Ahead should also say something like "the "additional suffix" only
          // contains writes, i.e. you cannot read the future
          assume (A_R? y);
          let msg = next_message tr tr_w in
          let q' = step q msg in
          let tr_new = extend tr msg in
          assert (y == A_R q' tr_new);
          let z' = {to = q'; tr = tr_new} in
          //assert (({to = q'; tr = tr_new}) `extended_to` ({to = q_w; tr = tr_w}));
          admit()
        ) else admit()
    in Classical.forall_intro (Classical.move_requires aux)

let f_a_r (#p:dprot) (q:dprot{is_recv q /\ more q}) (tr:trace p q)
  (v:t p{compatible (pcm p) (A_R q tr) v})
  : GTot (y:t p{compatible (pcm p) y v /\ frame_compatible (A_R q tr) v y})
  = match v with
    | A_R q tr -> A_R q tr
    | V tr' ->
        lemma_compatible_a_greater_length q tr tr';
        if trace_length tr >= trace_length tr'.tr then
          // No new message yet
          A_R q tr
        else
          let y = extend_node_a_r tr tr' in
          frame_compatible_a_extend q tr tr';
          y

val get_a_r (#p:dprot) (c:chan p) (q:dprot{is_recv q /\ more q}) (tr:trace p q)
  : SteelT (tr':partial_trace_of p{compatible (pcm p) (A_R q tr) (V tr')})
           (pts_to c (A_R q tr))
           (fun tr' ->
             if trace_length tr >= trace_length tr'.tr then
               pts_to c (A_R q tr)
             else pts_to c (extend_node_a_r tr tr'))

let get_a_r #p c q tr =
  let v = select_refine c (A_R q tr) (f_a_r q tr) in
  let (tr':partial_trace_of p{compatible (pcm p) (A_R q tr) (V tr')}) = V?._0 v in
  change_slprop
    (pts_to c (f_a_r q tr v))
    (if trace_length tr >= trace_length tr'.tr then pts_to c (A_R q tr) else pts_to c (extend_node_a_r tr tr'))
    (fun _ -> ());
  tr'

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
    (ahead_refl p (empty_trace p)) ();
  r

val send_a
  (#p:dprot)
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

val recv_a
  (#p:dprot)
  (c:chan p)
  (next:dprot{more next /\ tag_of next = Recv})
  (tr:trace p next)
  : SteelT (msg_t next)
           (endpoint_a c next tr)
           (fun x -> endpoint_a c (step next x) (extend tr x))

let rec recv_a #p c next tr =
  change_slprop (endpoint_a c next tr) (pts_to c (A_R next tr)) (fun _ -> ());
  let tr' = get_a_r c next tr in
  cond (trace_length tr >= trace_length tr'.tr)
    // Problem: The second precondition requires (not b) to typecheck
    (fun b ->
      if b then pts_to c (A_R next tr)
      else (pts_to c (extend_node_a_r tr tr'))
    )
    (fun _ x -> endpoint_a c (step next x) (extend tr x))
    (fun _ ->
      change_slprop (pts_to c (A_R next tr)) (endpoint_a c next tr) (fun _ -> ());
      recv_a c next tr)
    (fun _ ->
      let x = next_message tr tr' in
      change_slprop
        (pts_to c (extend_node_a_r tr tr'))
        (endpoint_a c (step next x) (extend tr x))
        (fun _ -> ());
      x
    )
