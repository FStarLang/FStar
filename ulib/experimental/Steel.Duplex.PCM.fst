module Steel.Duplex.PCM

open FStar.PCM

open Steel.Channel.Protocol

let dprot' = protocol unit

module WF = FStar.WellFounded
module P = FStar.Preorder
module R = FStar.ReflexiveTransitiveClosure

// Simplifying protocols for now
let rec no_loop (p:dprot') = match p with
  | Return _ -> False
  | Msg _ a k -> (forall x. (WF.axiom1 k x; no_loop (k x)))
  | DoWhile _ _ -> False

let dprot = p:dprot'{no_loop p}

let is_send (p:dprot) = Msg? p && (Send? (Msg?._0 p))
let is_recv (p:dprot) = Msg? p && (Recv? (Msg?._0 p))

let empty_trace (p:dprot) : trace p p = Waiting p

let partial_trace_of (p:dprot) = tr:partial_trace_of p{no_loop tr.to}

type party = | A | B

let next (tag:party) (#p:dprot) : P.relation (partial_trace_of p) =
  fun (t0 t1: partial_trace_of p) ->
    more_msgs t0.to /\
    // Ensuring that if we are ahead, we only have writes
    (if A? tag then is_send t0.to else is_recv t0.to) /\
    (exists (msg:next_msg_t t0.to).
      t1.to == step t0.to msg /\
      t1.tr == extend t0.tr msg)

let extended_to (tag:party) (#p:dprot) : P.preorder (partial_trace_of p) =
  R.closure (next tag #p)


noeq
type t (p:dprot) =
 | V : partial_trace_of p -> t p
 | A_W : q:dprot {is_send q} -> trace p q -> t p
 | A_R : q:dprot {is_recv q} -> trace p q -> t p
 | B_R : q:dprot {is_send q} -> trace p q -> t p
 | B_W : q:dprot {is_recv q} -> trace p q -> t p
 | Nil

let ahead (tag:party) (#p:dprot) (q q':dprot) (s:trace p q) (s':trace p q') : prop
  = ({ to = q'; tr = s'} `extended_to tag` { to = q; tr = s }) /\ True

let ahead_refl (tag:party) (#p:dprot) (q:dprot) (s:trace p q)
  : Lemma (ahead tag q q s s)
  = ()

let rec trace_length #p #q (s:trace p q) : Tot nat (decreases s) = match s with
  | Waiting _ -> 0
  | Message _ _ _ t -> 1 + trace_length t

let composable #p : symrel (t p) = fun t0 t1 ->
    match t0, t1 with
    | _, Nil
    | Nil, _ -> True
    | A_W q s, B_R q' s'
    | B_R q' s', A_W q s -> ahead A q q' s s'
    | B_W q s, A_R q' s'
    | A_R q' s', B_W q s -> ahead B q q' s s'
    | A_R q s, B_R q' s'
    | B_R q' s', A_R q s -> ahead A q q' s s' \/ ahead B q' q s' s
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

#push-options "--z3rlimit 20"

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

#pop-options

let refine (#prot:dprot) (x:t prot) : prop = V? x \/ Nil? x

let pcm (prot:dprot) : pcm (t prot) =
  { p = p' prot;
    comm = lemma_comm;
    assoc = lemma_assoc_l;
    assoc_r = lemma_assoc_r;
    is_unit = lemma_is_unit;
    refine = refine
}

open Steel.Memory
open Steel.Effect
open FStar.Ghost

let chan (p:dprot) = ref (t p) (pcm p)

assume val pts_to (#p:dprot) (r:chan p) (v:(t p)) : slprop u#1

let endpoint_a (#p:dprot) (c:chan p) (next:dprot) (tr:trace p next) =
  pts_to c (if is_send next then A_W next tr else A_R next tr)

let endpoint_b (#p:dprot) (c:chan p) (next:dprot) (tr:trace p next) =
  pts_to c (if is_send next then B_R next tr else B_W next tr)


// From nik_fictional

let frame_compatible (#p:dprot) (x:t p) (v y:t p) =
  (forall (frame:t p). {:pattern (composable x frame)}
            composable x frame /\
            v == compose x frame ==>
            composable y frame /\
            v == compose y frame)

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
  (#from:dprot) (#to #to':dprot)
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
  (#from #to:dprot)
  (tr:trace from to)
  : Lemma (ensures is_trace_prefix tr tr)
          (decreases tr)
  = match tr with
    | Waiting _ -> ()
    | Message _ _ _ tail -> lemma_is_trace_prefix_refl tail

let rec lemma_is_trace_prefix_extend (#from #to #to':dprot)
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
    ()

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
  (tag:party)
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to')
  : Lemma (requires ahead tag to' to tr' tr)
          (ensures is_trace_prefix tr tr')
  = let stable (z:partial_trace_of from) : Type0 = is_trace_prefix tr z.tr in
    let aux (y z:partial_trace_of from)
      : Lemma (requires stable y /\ next tag y z)
              (ensures stable z)
      = Classical.forall_intro (Classical.move_requires (lemma_is_trace_prefix_extend tr y.tr))
   in Classical.forall_intro_2 (Classical.move_requires_2 aux);
   let open FStar.ReflexiveTransitiveClosure in
   stable_on_closure (next tag) stable ();
   lemma_is_trace_prefix_refl tr

let next_message
  (#from:dprot) (#to #to':dprot)
  (tr:trace from to)
  (tr':trace from to'{trace_length tr' > trace_length tr /\
    (exists tag. ahead tag to' to tr' tr)})
  = Classical.forall_intro (fun tag -> Classical.move_requires (lemma_ahead_implies_trace_prefix tag tr) tr');
    next_message_aux tr tr'

let rec extend_increase_length (#from #to:dprot) (t:trace from to{more_msgs to}) (m:next_msg_t to)
  : Lemma (ensures trace_length (extend t m) == trace_length t + 1)
          (decreases t)
  = match t with
    | Waiting _ -> ()
    | Message _ _ _ tail -> extend_increase_length tail m

let next_increase_length (tag:party) (#p:dprot) (x y:partial_trace_of p)
  : Lemma (requires next tag x y)
          (ensures trace_length y.tr == trace_length x.tr + 1)
  = let aux (msg:next_msg_t x.to)
        : Lemma (requires y.to == step x.to msg /\ y.tr == extend x.tr msg)
                (ensures trace_length y.tr == trace_length x.tr + 1)
        = extend_increase_length x.tr msg
    in Classical.forall_intro (Classical.move_requires aux)

let rec lemma_ahead_is_longer (tag:party) (#p:dprot) (q:dprot) (s:trace p q) (q':dprot) (s':trace p q')
  : Lemma (requires ahead tag q q' s s')
          (ensures trace_length s >= trace_length s')
  = let open FStar.ReflexiveTransitiveClosure in
    let l = ({to = q'; tr = s'}) in
    let r = ({to = q; tr = s}) in
    let stable_p (x:partial_trace_of p) : Type0 = trace_length x.tr >= trace_length s' in
    let aux (x y:partial_trace_of p)
      : Lemma (requires stable_p x /\ next tag x y)
              (ensures stable_p y)
      = next_increase_length tag x y
    in Classical.forall_intro_2 (fun x -> Classical.move_requires (aux x));
    stable_on_closure (next tag) stable_p ()


let compatible_a_r_v_is_ahead
  (#p:dprot) (#q:dprot{is_recv q}) (tr:trace p q)
  (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (A_R q tr) (V tr'))
          (ensures ahead B tr'.to q tr'.tr tr)
  =  let aux (frame:t p) : Lemma
        (requires composable (A_R q tr) frame /\ compose frame (A_R q tr) == V tr')
        (ensures ahead B tr'.to q tr'.tr tr)
        = assert (B_R? frame \/ B_W? frame);
          if B_W? frame then ()
          else (
            let q' = B_R?.q frame in
            let tr' = B_R?._1 frame in
            if trace_length tr' >= trace_length tr then
              Classical.move_requires (lemma_ahead_is_longer A q tr q') tr'
            else ahead_refl B q tr
         )
    in
    Classical.forall_intro (Classical.move_requires aux)

let rec lemma_same_trace_length_ahead_refl' (#p:dprot) (#q #q':dprot)
  (s:trace p q)
  (s':trace p q')
  : Lemma (requires is_trace_prefix s s' /\ trace_length s == trace_length s')
          (ensures q == q' /\ s == s')
          (decreases s)
  =  match s with
    | Waiting _ -> ()
    | Message _ _ _ _ ->
        lemma_same_trace_length_ahead_refl' (Message?._3 s) (Message?._3 s')

let lemma_same_trace_length_ahead_refl (tag:party) (#p:dprot) (#q #q':dprot)
  (s:trace p q)
  (s':trace p q')
  : Lemma (requires ahead tag q q' s s' /\ trace_length s == trace_length s')
          (ensures q == q' /\ s == s')
  = lemma_ahead_implies_trace_prefix tag s' s;
    lemma_same_trace_length_ahead_refl' s' s

let compatible_b_r_v_is_ahead
  (#p:dprot) (#q:dprot{is_send q}) (tr:trace p q)
  (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (B_R q tr) (V tr'))
          (ensures ahead A tr'.to q tr'.tr tr)
  = let aux (frame:t p) : Lemma
        (requires composable (B_R q tr) frame /\ compose frame (B_R q tr) == V tr')
        (ensures ahead A tr'.to q tr'.tr tr)
        = assert (A_R? frame \/ A_W? frame);
          if A_W? frame then ()
          else (
            let q_a = A_R?.q frame in
            let tr_a = A_R?._1 frame in
            if trace_length tr_a > trace_length tr then (
              Classical.move_requires (lemma_ahead_is_longer B q tr q_a) tr_a
            ) else if trace_length tr_a < trace_length tr then ahead_refl A q tr
              else (
                assert (tr'.to == q_a /\ tr'.tr == tr_a);
                // We need both sides, since there is a disjunction in the PCM in the A_R/B_R case
                Classical.move_requires (lemma_same_trace_length_ahead_refl A tr_a) tr;
                Classical.move_requires (lemma_same_trace_length_ahead_refl B tr) tr_a;
                assert (q == q_a /\ tr == tr_a);
                ahead_refl A q tr
              )
         )
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

let extend_node_b_r (#p:dprot) (#q:dprot{more q /\ is_send q}) (tr:trace p q)
  (tr':partial_trace_of p{trace_length tr'.tr > trace_length tr /\
    compatible (pcm p) (B_R q tr) (V tr')})
  : (y:t p)
  = compatible_b_r_v_is_ahead tr tr';
    let x = next_message tr tr'.tr in
    let q' = step q x in
    let tr' = extend tr x in
    if is_send q' then B_R q' tr' else B_W q' tr'


let lemma_compatible_a_greater_length (#p:dprot) (q:dprot{is_recv q}) (tr:trace p q) (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (A_R q tr) (V tr'))
          (ensures trace_length tr'.tr >= trace_length tr)
  = compatible_a_r_v_is_ahead tr tr';
    lemma_ahead_is_longer B tr'.to tr'.tr q tr

let lemma_compatible_b_greater_length (#p:dprot) (q:dprot{is_send q}) (tr:trace p q) (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (B_R q tr) (V tr'))
          (ensures trace_length tr'.tr >= trace_length tr)
  = compatible_b_r_v_is_ahead tr tr';
    lemma_ahead_is_longer A tr'.to tr'.tr q tr

let rec lemma_unique_next_common_prefix
  (tag:party)
  (#p:dprot)
  (tr z tr':partial_trace_of p)
  : Lemma (requires is_trace_prefix tr.tr tr'.tr /\ is_trace_prefix z.tr tr'.tr /\
                    next tag tr z /\ trace_length tr'.tr > trace_length tr.tr)
          (ensures (
            let x = next_message_aux tr.tr tr'.tr in
            let tr2 = extend tr.tr x in
            z.to == step tr.to x /\
            tr2 == z.tr)
          )
          (decreases tr.tr)
  = let Message _ x_z _ tail_z = z.tr in
    let Message _ x' _ tail' = tr'.tr in
    match tr.tr with
    | Waiting _ -> ()
    | Message _ _ to tail -> lemma_unique_next_common_prefix tag
      ({to = to; tr = tail}) ({to = z.to; tr = tail_z}) ({to = tr'.to; tr = tail'})

let next_message_closure (tag:party) (#p:dprot) (tr tr':partial_trace_of p)
  : Lemma (requires trace_length tr'.tr > trace_length tr.tr /\ tr `extended_to tag` tr')
          (ensures (
            let x = next_message tr.tr tr'.tr in
            let q2 = step tr.to x in
            let tr2 = extend tr.tr x in
            ({to = q2; tr = tr2}) `extended_to tag` tr'))
  = let x = next_message tr.tr tr'.tr in
    let q2 = step tr.to x in
    let tr2 = extend tr.tr x in
    let z_new = {to = q2; tr = tr2} in
    let open FStar.ReflexiveTransitiveClosure in
    assert (exists z. next tag tr z /\ z `extended_to tag` tr');
    let aux (z:partial_trace_of p)
      : Lemma (requires next tag tr z /\ z `extended_to tag` tr')
              (ensures z == z_new)
      = lemma_ahead_implies_trace_prefix tag z.tr tr'.tr;
        lemma_ahead_implies_trace_prefix tag tr.tr tr'.tr;
        lemma_unique_next_common_prefix tag tr z tr'
    in Classical.forall_intro (Classical.move_requires aux)

let lemma_same_length_ahead_implies_eq (#p:dprot) (tr tr':partial_trace_of p)
  : Lemma (requires trace_length tr.tr == trace_length tr'.tr /\ is_trace_prefix tr.tr tr'.tr)
          (ensures tr == tr')
  = let rec aux (#p #q1 #q2:dprot) (tr1:trace p q1) (tr2:trace p q2)
        : Lemma (requires trace_length tr1 == trace_length tr2 /\ is_trace_prefix tr1 tr2)
                (ensures q1 == q2 /\ tr1 == tr2)
                (decreases tr1)
        = match tr1 with
          | Waiting _ -> ()
          | Message _ _ _ tail -> aux tail (Message?._3 tr2)
    in aux tr.tr tr'.tr

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
          next_message_closure B p_tr tr'
          // The PCM gives us here that y has to be A_R, it cannot be A_W
          // because then there would be a B read in the trace ahead of x

        ) else (
          let q_b = B_R?.q frame in
          let tr_b = B_R?._1 frame in
          assert (tr' == {to = q_b; tr = tr_b});
          Classical.move_requires (lemma_ahead_is_longer A q tr q_b) tr_b;
          // Gives us the following assertion by contraposition
          assert (p_tr `extended_to B` tr');
          next_message_closure B p_tr tr';

          if A_W? y then (
            ahead_refl B q_b tr_b
          ) else (
            let A_R q_a tr_a = y in
            lemma_ahead_is_longer B q_b tr_b q_a tr_a;
            lemma_ahead_implies_trace_prefix B tr_a tr_b;
            Classical.move_requires (lemma_same_length_ahead_implies_eq ({to = q_a; tr = tr_a})) tr'
          )
        )
    in Classical.forall_intro (Classical.move_requires aux)

let frame_compatible_b_extend (#p:dprot)
  (q:dprot{is_send q /\ more q}) (tr:trace p q)
  (tr':partial_trace_of p)
  : Lemma (requires compatible (pcm p) (B_R q tr) (V tr') /\ trace_length tr'.tr > trace_length tr)
          (ensures frame_compatible (B_R q tr) (V tr') (extend_node_b_r tr tr'))
  = let x = B_R q tr in
    let p_tr:partial_trace_of p = {to = q; tr = tr} in
    let v = V tr' in
    let y = extend_node_b_r tr tr' in
    let aux (frame:t p)
      : Lemma (requires composable x frame /\ v == compose x frame)
              (ensures composable y frame /\ v == compose y frame)
      = assert (A_R? frame \/ A_W? frame);
        if A_W? frame then (
          next_message_closure A p_tr tr'
          // The PCM gives us here that y has to be B_R, it cannot be B_W
          // because then there would be a A read in the trace ahead of x

        ) else (
          let q_a = A_R?.q frame in
          let tr_a = A_R?._1 frame in
          assert (tr' == {to = q_a; tr = tr_a});
          Classical.move_requires (lemma_ahead_is_longer B q tr q_a) tr_a;
          // Gives us the following assertion by contraposition
          assert (p_tr `extended_to A` tr');
          next_message_closure A p_tr tr';

          if B_W? y then (
            ahead_refl A q_a tr_a
          ) else (
            let B_R q_b tr_b = y in
            lemma_ahead_is_longer A q_a tr_a q_b tr_b;
            lemma_ahead_implies_trace_prefix A tr_b tr_a;
            Classical.move_requires (lemma_same_length_ahead_implies_eq ({to = q_b; tr = tr_b})) tr'
          )
        )
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

let f_b_r (#p:dprot) (q:dprot{is_send q /\ more q}) (tr:trace p q)
  (v:t p{compatible (pcm p) (B_R q tr) v})
  : GTot (y:t p{compatible (pcm p) y v /\ frame_compatible (B_R q tr) v y})
  = match v with
    | B_R q tr -> B_R q tr
    | V tr' ->
        lemma_compatible_b_greater_length q tr tr';
        if trace_length tr >= trace_length tr'.tr then
          // No new message yet
          B_R q tr
        else
          let y = extend_node_b_r tr tr' in
          frame_compatible_b_extend q tr tr';
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

val get_b_r (#p:dprot) (c:chan p) (q:dprot{is_send q /\ more q}) (tr:trace p q)
  : SteelT (tr':partial_trace_of p{compatible (pcm p) (B_R q tr) (V tr')})
           (pts_to c (B_R q tr))
           (fun tr' ->
             if trace_length tr >= trace_length tr'.tr then
               pts_to c (B_R q tr)
             else pts_to c (extend_node_b_r tr tr'))

let get_b_r #p c q tr =
  let v = select_refine c (B_R q tr) (f_b_r q tr) in
  let (tr':partial_trace_of p{compatible (pcm p) (B_R q tr) (V tr')}) = V?._0 v in
  change_slprop
    (pts_to c (f_b_r q tr v))
    (if trace_length tr >= trace_length tr'.tr then pts_to c (B_R q tr) else pts_to c (extend_node_b_r tr tr'))
    (fun _ -> ());
  tr'

assume
val write_a
  (#p:dprot)
  (r:chan p)
  (#next:dprot{more next /\ tag_of next = Send})
  (tr:trace p next)
  (x:msg_t next)
  :SteelT unit (pts_to r (A_W next tr)) (fun _ -> endpoint_a r (step next x) (extend tr x))

assume
val write_b
  (#p:dprot)
  (r:chan p)
  (#next:dprot{more next /\ tag_of next = Recv})
  (tr:trace p next)
  (x:msg_t next)
  :SteelT unit (pts_to r (B_W next tr)) (fun _ -> endpoint_b r (step next x) (extend tr x))

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
    (ahead_refl A p (empty_trace p)) ();
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
  cond #(msg_t next) (trace_length tr >= trace_length tr'.tr)
    (fun b ->
      if b then pts_to c (A_R next tr)
      else (pts_to c (extend_node_a_r tr tr'))
    )
    (fun _ x -> endpoint_a c (step next x) (extend tr x))
    (fun _ ->
      change_slprop (pts_to c (A_R next tr)) (endpoint_a c next tr) (fun _ -> ());
      recv_a c next tr)
    (fun _ ->
      compatible_a_r_v_is_ahead tr tr';
      let x = next_message tr tr'.tr in
      change_slprop
        (pts_to c (extend_node_a_r tr tr'))
        (endpoint_a c (step next x) (extend tr x))
        (fun _ -> ());
      x
    )


val send_b
  (#p:dprot)
  (c:chan p)
  (#next:dprot{more next /\ tag_of next = Recv})
  (x:msg_t next)
  (tr:trace p next)
  : SteelT unit
           (endpoint_b c next tr)
           (fun _ -> endpoint_b c (step next x) (extend tr x))

let send_b #p c #next x tr =
  change_slprop (endpoint_b c next tr) (pts_to c (B_W next tr)) (fun _ -> ());
  write_b c tr x

val recv_b
  (#p:dprot)
  (c:chan p)
  (next:dprot{more next /\ tag_of next = Send})
  (tr:trace p next)
  : SteelT (msg_t next)
           (endpoint_b c next tr)
           (fun x -> endpoint_b c (step next x) (extend tr x))

let rec recv_b #p c next tr =
  change_slprop (endpoint_b c next tr) (pts_to c (B_R next tr)) (fun _ -> ());
  let tr' = get_b_r c next tr in
  cond #(msg_t next) (trace_length tr >= trace_length tr'.tr)
    (fun b ->
      if b then pts_to c (B_R next tr)
      else (pts_to c (extend_node_b_r tr tr'))
    )
    (fun _ x -> endpoint_b c (step next x) (extend tr x))
    (fun _ ->
      change_slprop (pts_to c (B_R next tr)) (endpoint_b c next tr) (fun _ -> ());
      recv_b c next tr)
    (fun _ ->
      compatible_b_r_v_is_ahead tr tr';
      let x = next_message tr tr'.tr in
      change_slprop
        (pts_to c (extend_node_b_r tr tr'))
        (endpoint_b c (step next x) (extend tr x))
        (fun _ -> ());
      x
    )
