module Steel.Channel.Simplex
module P = Steel.Channel.Protocol
open Steel.SpinLock
open Steel.Effect
open Steel.Memory
open Steel.HigherReference
open Steel.SteelT.Basics

module T = FStar.Tactics
module ST = Steel.Memory.Tactics

(* Some helpers *)
private
val reshuffle0 (#p #q : hprop)
              (_ : squash (p `equiv` q))
   : SteelT unit p (fun _ -> q)

private
let reshuffle0 #p #q peq =
  Steel.SteelAtomic.Basics.lift_atomic_to_steelT
    (fun () -> Steel.Effect.Atomic.change_hprop p q (fun m -> ()))

private
val reshuffle (#p #q : hprop)
              (_ : squash (T.with_tactic ST.canon
                                         (squash (p `equiv` q))))
   : SteelT unit p (fun _ -> q)

#push-options "--no_tactics" (* GM: This should not be needed *)

private
let reshuffle #p #q peq =
  T.by_tactic_seman ST.canon (squash (p `equiv` q));
  reshuffle0 ()

#pop-options

////////////////////////////////////////////////////////////////////////////////
// Some generic lemmas
////////////////////////////////////////////////////////////////////////////////
let assoc_r (p q r:hprop)
  : SteelT unit ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = reshuffle ()

let assoc_l (p q r:hprop)
  : SteelT unit (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = reshuffle ()

let pts_to_injective #a #p #q (r:ref a) (v0 v1:Ghost.erased a) (rest:Ghost.erased a -> hprop)
  : SteelT unit (pts_to r p v0 `star` pts_to r q v1 `star` rest v1)
                (fun _ -> pts_to r p v0 `star` pts_to r q v0 `star` rest v0)
  = Steel.SteelAtomic.Basics.lift_atomic_to_steelT
      (fun () -> Steel.Effect.Atomic.change_hprop _ _
                (fun m -> pts_to_ref_injective r p q v0 v1 m;
                       assert (v0 == v1)))

let ghost_read_refine (#a:Type) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT (Ghost.erased a) (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = let x = read_refine q r in
    return (Ghost.hide x)


val intro_pure_p (#p:prop) (s:squash p) (h:hprop)
  : SteelT unit h (fun _ -> pure p `star` h)
let intro_pure_p #p s h =
  let s : squash (h `equiv` (pure p `star` h)) =
    lem_star_pure h p;
    star_commutative h (pure p)
  in
  reshuffle0 s

val elim_pure (#p:prop)
  : SteelT (squash p) (pure p) (fun _ -> emp)
let elim_pure #p =
  assert (exists m. interp (pure p) m);
  FStar.Classical.forall_intro (FStar.Classical.move_requires (lem_interp_star_pure emp p));
  reshuffle ();
  h_affine emp (pure p);
  ()

val intro_pure (#p:prop) (s:squash p)
  : SteelT unit emp (fun _ -> pure p)
let intro_pure #p s =
  intro_pure_p #p s emp;
  reshuffle ()

let elim_intro_pure (#p:prop)
  : SteelT (squash p) (pure p) (fun _ -> pure p)
  = let s = elim_pure #p in
    intro_pure #p s;
    s

let dup_pure (p:prop)
  : SteelT unit (pure p) (fun _ -> pure p `star` pure p)
  = let s = elim_intro_pure #p in
    intro_pure_p s _

let rewrite_ext (p q:hprop) (_:squash (p == q))
  : SteelT unit p (fun _ -> q)
  = return ()

let h_exists_assoc_r (#a:Type) (p q r: a -> hprop)
  : SteelT unit (h_exists (fun x -> p x `star` q x `star` r x))
                (fun _ -> h_exists (fun x -> p x `star` (q x `star` r x)))
  = let aux (x:a) : Lemma ((p x `star` q x `star` r x) `equiv` (p x `star` (q x `star` r x)))
        = ST.shuffled (p x `star` q x `star` r x) (p x `star` (q x `star` r x))
    in
    let peq : squash ((h_exists (fun x -> p x `star` q x `star` r x))
                      `equiv`
                      (h_exists (fun x -> p x `star` (q x `star` r x))))
      = FStar.Classical.forall_intro aux;
        Steel.Memory.h_exists_cong (fun x -> p x `star` q x `star` r x) (fun x -> p x `star` (q x `star` r x))
    in
    reshuffle0 peq

let rearrange_for_get_trace2 (p q r s t : hprop)
  : SteelT unit ((p `star` q) `star` (r `star` s `star` t))
                (fun _ -> (r `star` s `star` p `star` t) `star` q)
  = reshuffle ()


let rearrange_for_get_trace (p q r s : hprop)
  : SteelT unit (p `star` q `star` r `star` s)
                (fun _ -> r `star` (p `star` q `star` s))
  = reshuffle ()

////////////////////////////////////////////////////////////////////////////////

let sprot = p:prot { more p }

noeq
type chan_val = {
  chan_prot : sprot;
  chan_msg  : msg_t chan_prot;
  chan_ctr  : nat
}

let trace_ref (p:prot) = reference (partial_trace_of p) extended_to

noeq
type chan_t (p:prot) = {
  send: ref chan_val;
  recv: ref chan_val;
  trace: trace_ref p;
}

let half : perm u#1 = half_perm full

let step (s:sprot) (x:msg_t s) = step s x

let chan_inv_step_p (vrecv vsend:chan_val) : prop =
  (vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg /\
   vsend.chan_ctr == vrecv.chan_ctr + 1)

let chan_inv_step (vrecv vsend:chan_val) =
  pure (chan_inv_step_p vrecv vsend)

let chan_inv_cond (vsend:chan_val) (vrecv:chan_val) =
    if vsend.chan_ctr = vrecv.chan_ctr
    then pure (vsend == vrecv)
    else chan_inv_step vrecv vsend

let trace_until #p (r:trace_ref p) (vr:chan_val) =
  h_exists (fun (tr:partial_trace_of p) ->
                   pts_to_ref r full tr `star`
                   pure (until tr == step vr.chan_prot vr.chan_msg))

let chan_inv_recv #p (c:chan_t p) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star`
      trace_until c.trace vrecv `star`
      chan_inv_cond vsend vrecv)

let chan_inv #p (c:chan_t p) : hprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

let rewrite_eq_squash #a (x:a) (y:a{x==y}) (p:a -> hprop)
  : SteelT unit (p x) (fun _ -> p y)
  = h_assert (p y)

let intro_chan_inv_cond_eq (vs vr:chan_val)
  : SteelT unit (pure (vs == vr))
                (fun _ -> chan_inv_cond vs vr)
  = elim_pure #(vs==vr);
    assert (vs == vr);
    intro_pure #(vs == vs) ();
    h_assert (chan_inv_cond vs vs);
    rewrite_eq_squash vs vr (chan_inv_cond vs);
    h_assert (chan_inv_cond vs vr)

let intro_chan_inv_cond_step (vs vr:chan_val)
  : SteelT unit (chan_inv_step vr vs)
                (fun _ -> chan_inv_cond vs vr)
  = elim_intro_pure #(chan_inv_step_p vr vs);
    assert (chan_inv_step_p vr vs);
    h_assert (chan_inv_step vr vs);
    rewrite_ext (chan_inv_step vr vs) (chan_inv_cond vs vr) ()

let frame_l #a #q #r (f:unit -> SteelT a q r) (p:hprop)
  : SteelT a (p `star` q) (fun x -> p `star` r x)
  = h_commute _ _;
    let x = frame f _ in
    h_commute _ _;
    return x

let intro_chan_inv_aux #p (c:chan_t p) (vs vr:chan_val)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_cond vs vr)
                 (fun _ -> chan_inv c)
  = reshuffle ();
    frame (fun _ -> intro_h_exists vr (fun (vr:chan_val) -> pts_to c.recv half vr `star` trace_until c.trace vr `star` chan_inv_cond vs vr)) (pts_to c.send half vs);
    h_commute _ _;
    intro_h_exists vs _

let intro_chan_inv_step #p (c:chan_t p) (vs vr:chan_val)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_step vr vs)
                 (fun _ -> chan_inv c)
  = frame_l (fun _ -> intro_chan_inv_cond_step vs vr) _;
    intro_chan_inv_aux c vs vr

let intro_chan_inv_eq #p (c:chan_t p) (vs vr:chan_val)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 pure (vs == vr))
                 (fun _ -> chan_inv c)
  = frame_l (fun _ -> intro_chan_inv_cond_eq vs vr) _;
    intro_chan_inv_aux c vs vr


noeq
type chan p = {
  chan_chan : chan_t p;
  chan_lock : lock (chan_inv chan_chan)
}

let in_state_prop (p:prot) (vsend:chan_val) : prop =
  p == step vsend.chan_prot vsend.chan_msg

irreducible
let next_chan_val (#p:sprot) (x:msg_t p) (vs0:chan_val { in_state_prop p vs0 })
  : Tot (vs:chan_val{in_state_prop (step p x) vs /\ chan_inv_step_p vs0 vs})
  = {
      chan_prot = (step vs0.chan_prot vs0.chan_msg);
      chan_msg = x;
      chan_ctr = vs0.chan_ctr + 1
    }

let in_state_hprop (p:prot) (vsend:chan_val) : hprop = pure (in_state_prop p vsend)

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pts_to r half vsend `star` in_state_hprop p vsend)

let sender #q (c:chan q) (p:prot) = in_state c.chan_chan.send p
let receiver #q (c:chan q) (p:prot) = in_state c.chan_chan.recv p

let intro_chan_inv #p (c:chan_t p) (v:chan_val)
  : SteelT unit (pts_to c.send half v `star`
                 pts_to c.recv half v `star`
                 trace_until c.trace v)
                (fun _ -> chan_inv c)
  = intro_pure_p #(v==v) () _;
    h_commute _ _;
    intro_chan_inv_eq c v v

let chan_val_p (p:prot) = (vs0:chan_val { in_state_prop p vs0 })

let intro_in_state (r:ref chan_val) (p:prot) (v:chan_val_p p)
  : SteelT unit (pts_to r half v) (fun _ -> in_state r p)
  = intro_pure_p #(in_state_prop p v) () _;
    h_commute _ _;
    intro_h_exists v _

let eq #a (x y : a) :prop = x == y

let rewrite_eq #a (x:a) (y:a) (p:a -> hprop)
  : SteelT unit (pure (eq x y) `star` p x) (fun _ -> p y)
  = let _ = frame (fun _ -> elim_pure #(eq x y)) (p x) in
    h_assert (emp `star` p x);
    h_commute _ _;
    h_affine _ _;
    h_assert (p x);
    assert (x == y);
    rewrite_eq_squash x y p

#push-options "--print_universes"



let mk_chan_t_val (#p:prot) (send recv:ref chan_val) (tr:trace_ref p)
  : SteelT (c:chan_t p{c==Mkchan_t send recv tr}) emp (fun c -> emp)
  = let c = (Mkchan_t send recv tr) in
    return #_ #(fun c -> emp) c

let msg t p = Msg unit (fun _ -> p)
let init_chan_val (p:prot) = v:chan_val {v.chan_prot == msg unit p}

let initial_trace (p:prot) : (q:partial_trace_of p {until q == p})
  = { to = p; tr=Waiting p}

let intro_until_eq #p (c:chan_t p) (v:init_chan_val p) //{p == step v.chan_prot v.chan_msg})
  : SteelT unit emp (fun _ -> pure (until (initial_trace p) == (step v.chan_prot v.chan_msg)))
  = let s :squash (until (initial_trace p) == (step v.chan_prot v.chan_msg)) = () in
    intro_pure #_ s

let intro_trace_until #q (r:trace_ref q) (tr:partial_trace_of q) (v:chan_val)
  : SteelT unit (pts_to_ref r full tr `star` pure (until tr == step v.chan_prot v.chan_msg))
                (fun _ -> trace_until r v)
  = intro_h_exists tr
                (fun (tr:partial_trace_of q) ->
                     pts_to_ref r full tr `star`
                     pure (until tr == (step v.chan_prot v.chan_msg)))

let intro_trace_until_init  #p (c:chan_t p) (v:init_chan_val p)
  : SteelT unit (pts_to_ref c.trace full (initial_trace p))
                (fun _ -> trace_until c.trace v)
  = h_intro_emp_l _;
    frame (fun _ -> intro_until_eq c v) _;
    h_assert (pure (until (initial_trace p) == (step v.chan_prot v.chan_msg)) `star`
              pts_to_ref c.trace full (initial_trace p));
    reshuffle ();
    intro_trace_until c.trace (initial_trace p) v

let chan_t_sr (p:prot) (send recv:ref chan_val) = (c:chan_t p{c.send == send /\ c.recv == recv})
let mk_chan_t (#p:prot) (send recv:ref chan_val) (v:init_chan_val p)
  : SteelT (c:chan_t_sr p send recv)
           (pts_to send half v `star` pts_to recv half v)
           (fun c -> chan_inv c)
  = h_intro_emp_l _;
    let tr : trace_ref p = frame (fun _ -> alloc_monotonic_ref (extended_to #p) (initial_trace p)) _ in
    h_assert (pts_to_ref tr full (initial_trace p) `star` (pts_to send half v `star` pts_to recv half v));
    h_intro_emp_l _;
    let c = frame (fun _ -> mk_chan_t_val #p send recv tr) _ in
    h_elim_emp_l _;
    h_assert ((pts_to_ref c.trace full (initial_trace p) `star` (pts_to c.send half v `star` pts_to c.recv half v)));
    frame (fun _ -> intro_trace_until_init c v) _;
    h_assert (trace_until c.trace v `star` (pts_to c.send half v `star` pts_to c.recv half v));
    reshuffle ();
    intro_chan_inv c v;
    let c' : chan_t_sr p send recv = c in
    return #(chan_t_sr p send recv) #(fun c -> chan_inv c) c'

open Steel.Permissions
let new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)
  = let q = msg unit p in
    let v : chan_val = { chan_prot = q; chan_msg = (); chan_ctr = 0 } in
    let vp : init_chan_val p = v in
    let send = alloc v in
    h_assert (pts_to send full v);
    h_intro_emp_l (pts_to send full v);
    let recv = frame (fun _ -> alloc v) _ in //(pts_to send full v) in
    h_assert (pts_to recv full v `star` pts_to send full v);
    let _  = frame (fun _ -> share recv) _ in //(pts_to send full v) in
    h_assert ((pts_to recv half v `star` pts_to recv half v) `star` pts_to send full v);
    h_commute _ _;
    let _  = frame (fun _ -> share send) _ in
    h_assert ((pts_to send half v `star` pts_to send half v) `star`
              (pts_to recv half v `star` pts_to recv half v));
    reshuffle ();
    let c : chan_t_sr p send recv = frame (fun _ -> mk_chan_t #p send recv vp) _ in
    h_assert (chan_inv c `star` (pts_to send half v `star` pts_to recv half v));
    reshuffle ();
    h_assert (pts_to send half v `star` (pts_to recv half v `star` chan_inv c));
    let vp : chan_val_p p = v in
    h_assert (pts_to send half vp `star` (pts_to recv half vp `star` chan_inv c));
    frame (fun _ -> intro_in_state send p vp) _; //(pts_to recv half v `star` chan_inv c) in
    h_assert (in_state send p `star` (pts_to recv half v `star` chan_inv c));
    reshuffle ();
    let _ = frame (fun _ -> intro_in_state recv p vp) _ in
    h_assert (in_state recv p `star` (chan_inv c `star` in_state send p));
    reshuffle ();
    h_assert (chan_inv c `star` (in_state send p `star` in_state recv p));
    let l : lock (chan_inv c) = frame (fun _ -> new_lock (chan_inv c)) _ in
    let ch : chan p = { chan_chan = c; chan_lock = l } in
    h_assert (emp `star` (in_state send p `star` in_state recv p));
    reshuffle ();
    rewrite_eq_squash send ch.chan_chan.send (fun s -> in_state s p `star` in_state recv p);
    rewrite_eq_squash recv ch.chan_chan.recv (fun r -> in_state ch.chan_chan.send p `star` in_state r p);
    h_assert (sender ch p `star` receiver ch p);
    return #(chan p) #(fun ch -> (sender ch p `star` receiver ch p)) ch

let send_pre (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   trace_until c.trace vr `star`
   chan_inv_cond vs vr `star`
   in_state r p)

let send_pre_split (r:ref chan_val)  (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val) (b:bool) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   trace_until c.trace vr `star`
   (if b then pure (vs == vr) else chan_inv_step vr vs) `star`
   in_state r p)

let send_recv_in_sync (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     pure (vs == vr) `star`
     in_state r p)

let sender_ahead (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     chan_inv_step vr vs `star`
     in_state r p)

let channel_cases (r:ref chan_val) (#p:prot{more p}) #q (c:chan q) (x:msg_t p) (vs vr:chan_val)
                  (then_: (unit -> SteelT unit (send_recv_in_sync r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
                  (else_: (unit -> SteelT unit (sender_ahead r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
    : SteelT unit (send_pre r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_

let gather (#a:Type) (#v0 #v1:Ghost.erased a) (r:ref a)
  : SteelT unit
    (pts_to r half v0 `star` pts_to r half v1)
    (fun _ -> pts_to r full v0)
  = gather r

let share (#a:Type) (#v:a) (r:ref a)
  : SteelT unit
    (pts_to r full v)
    (fun _ -> pts_to r half v `star` pts_to r half v)
  = share r

let update_channel (#p:sprot) #q (c:chan_t q) (x:msg_t p) (vs:chan_val) (r:ref chan_val)
  : SteelT chan_val
           (pts_to r full vs `star` in_state_hprop p vs)
           (fun vs' -> pts_to r full vs' `star` (in_state_hprop (step p x) vs' `star` chan_inv_step vs vs'))
  = h_commute _ _;
    frame (fun _ -> elim_pure #(in_state_prop p vs)) _;
    h_elim_emp_l _;
    let vs' = next_chan_val x vs in
    write r vs';
    intro_pure_p #(in_state_prop (step p x) vs') () _;
    h_commute _ _;
    h_assert (pts_to r full vs' `star` in_state_hprop (step p x) vs');
    intro_pure_p #(chan_inv_step_p vs vs') () _;
    h_assert (chan_inv_step vs vs' `star` (pts_to r full vs' `star` in_state_hprop (step p x) vs'));
    reshuffle ();
    h_assert (pts_to r full vs' `star` (in_state_hprop (step p x) vs' `star` chan_inv_step vs vs'));
    return #chan_val #(fun vs' -> pts_to r full vs' `star` (in_state_hprop (step p x) vs' `star` chan_inv_step vs vs')) vs'

let send_pre_available (p:sprot) #q (c:chan_t q) (vs vr:chan_val)  = send_recv_in_sync c.send p c vs vr

let gather_r (#p:sprot) (r:ref chan_val) (v:chan_val)
  : SteelT unit
    (pts_to r half v `star` in_state r p)
    (fun _ -> pts_to r full v `star` in_state_hprop p v)
  = h_commute _ _;
    h_assert (in_state r p `star` pts_to r half v);
    let v' = frame (fun _ -> ghost_read_refine (in_state_hprop p) r) _ in
    h_assert ((pts_to r half v' `star` in_state_hprop p v') `star` pts_to r half v);
    reshuffle ();
    h_assert ((pts_to r half v `star` pts_to r half v') `star` in_state_hprop p v');
    pts_to_injective #_ #half #half r (Ghost.hide v) v' (fun (v':Ghost.erased chan_val) -> in_state_hprop p v');
    h_assert (pts_to r half v `star` pts_to r half v `star` in_state_hprop p v);
    frame (fun _ -> gather r) _

let send_available (#p:sprot) #q (cc:chan q) (x:msg_t p) (vs vr:chan_val) (_:unit)
  : SteelT unit (send_pre_available p #q cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = let c : chan_t q = cc.chan_chan in
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star`
              trace_until c.trace vr `star`
              pure (vs == vr) `star`
              in_state c.send p);
    reshuffle ();
    h_assert (pure (vs == vr) `star` (
               pts_to c.send half vs `star`
               pts_to c.recv half vr `star`
               trace_until c.trace vr `star`
               in_state c.send p));
    let _ = frame (fun _ -> elim_pure #(eq vs vr)) _ in
    assert (vs == vr);
    h_elim_emp_l _;
    rewrite_eq_squash vr vs (fun (vr:chan_val) ->
             pts_to c.send half vs `star`
             pts_to c.recv half vr `star`
             trace_until c.trace vr `star`
             in_state c.send p);
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vs `star`
              trace_until c.trace vs `star`
              in_state c.send p);
    reshuffle ();
    h_assert ((pts_to c.send half vs `star` in_state c.send p) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    frame (fun _ -> gather_r c.send vs) _;
    h_assert ((pts_to c.send full vs `star` in_state_hprop p vs) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    let next_vs = frame (fun _ -> update_channel c x vs c.send) _ in
    h_assert ((pts_to c.send full next_vs `star` (in_state_hprop (step p x) next_vs `star` chan_inv_step vs next_vs)) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    assoc_r _ _ _;
    frame (fun _ -> share #_ #next_vs c.send) _;
    h_assert ((pts_to c.send half next_vs `star` pts_to c.send half next_vs) `star`
               ((in_state_hprop (step p x) next_vs `star` chan_inv_step vs next_vs) `star`
                (pts_to c.recv half vs `star` trace_until c.trace vs)));
    reshuffle ();
    h_assert ((pts_to c.send half next_vs `star` in_state_hprop (step p x) next_vs) `star`
               ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                (pts_to c.recv half vs `star` trace_until c.trace vs)));
    frame (fun _ -> intro_h_exists next_vs (fun (next_vs:chan_val) -> pts_to c.send half next_vs `star` in_state_hprop (step p x) next_vs)) _;
    h_assert (sender cc (step p x) `star`
               ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                 (pts_to c.recv half vs `star` trace_until c.trace vs)));
    reshuffle ();
    frame (fun _ -> intro_chan_inv_step c next_vs vs) _;
    h_assert (chan_inv c `star` sender cc (step p x));
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _

let extensible (#p:prot) (x:partial_trace_of p) = P.more x.to
let next_msg_t (#p:prot) (x:partial_trace_of p) = P.next_msg_t x.to

let next_trace #p (vr:chan_val) (vs:chan_val)
                  (tr:partial_trace_of p)
                  (s:squash (eq (until tr) (step vr.chan_prot vr.chan_msg)))
                  (_:squash (chan_inv_step_p vr vs))
   : (ts:partial_trace_of p { until ts == step vs.chan_prot vs.chan_msg })
   = let msg : next_msg_t tr = vs.chan_msg in
     assert (extensible tr);
     extend_partial_trace tr msg

let squash_and (vr:chan_val) (vs:chan_val{chan_inv_step_p vr vs})
  : s:squash (chan_inv_step_p vr vs)
  = ()

let next_trace_st #p (vr:chan_val) (vs:chan_val) (tr:partial_trace_of p)
  : SteelT (extension_of tr)
           (chan_inv_step vr vs `star` pure (until tr == step vr.chan_prot vr.chan_msg))
           (fun ts -> pure (until ts == step vs.chan_prot vs.chan_msg))
  = let s0 : squash (chan_inv_step_p vr vs) =
       frame (fun _ -> elim_pure #(chan_inv_step_p vr vs)) _ in
    h_elim_emp_l _;
    let s1 : squash (until tr == step vr.chan_prot vr.chan_msg) =
      elim_pure #_ in
    let ts = next_trace vr vs tr s0 s1 in
    let s2 : squash (until ts == step vs.chan_prot vs.chan_msg) = () in
    intro_pure s2;
    h_assert (pure (until ts == step vs.chan_prot vs.chan_msg));
    return #(extension_of tr) #(fun ts -> pure (until ts == step vs.chan_prot vs.chan_msg)) ts

let write_trace #p (r:trace_ref p)
                   (old_tr:partial_trace_of p)
                   (new_tr:extension_of old_tr)
  : SteelT unit (pts_to_ref r full old_tr)
                (fun _ -> pts_to_ref r full new_tr)
  = let _ = write_monotonic_ref #_ #_ #old_tr r new_tr in
    return ()

let update_trace #p (r:trace_ref p) (vr:chan_val) (vs:chan_val) (s:squash (chan_inv_step_p vr vs))
  : SteelT unit
           (trace_until r vr) // `star` chan_inv_step vr vs)
           (fun _ -> trace_until r vs)
  = intro_pure_p s _;
    h_commute _ _;
    h_assert ((h_exists (fun (tr:partial_trace_of p) ->
                   pts_to_ref r full tr `star`
                   pure (until tr == step vr.chan_prot vr.chan_msg))) `star`
               chan_inv_step vr vs);
    let tr =
      frame (fun _ ->
        read_monotonic_ref #(partial_trace_of p) #full #(extended_to)
           #(fun (tr:partial_trace_of p) -> pure (eq (until tr) (step vr.chan_prot vr.chan_msg)))
           r) _
    in
    h_assert ((pts_to_ref r full tr `star` pure (eq (until tr) (step vr.chan_prot vr.chan_msg))) `star` chan_inv_step vr vs);
    assoc_r _ _ _;
    frame_l (fun _ -> h_commute _ _) _;
    let ts : extension_of tr = frame_l (fun _ -> next_trace_st vr vs tr) _ in
    h_assert (pts_to_ref r full tr `star` pure (until ts == step vs.chan_prot vs.chan_msg));
    frame (fun _ -> write_trace r tr ts) _;
    h_assert (pts_to_ref r full ts `star` pure (until ts == step vs.chan_prot vs.chan_msg));
    intro_h_exists ts (fun (ts:partial_trace_of p) ->
                         pts_to_ref r full ts `star`
                         pure (until ts == step vs.chan_prot vs.chan_msg))

let recv_available (#p:sprot) #q (cc:chan q) (vs vr:chan_val) (_:unit)
  : SteelT (msg_t p)
    (sender_ahead cc.chan_chan.recv p cc.chan_chan vs vr)
    (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star`
              trace_until c.trace vr `star`
              chan_inv_step vr vs `star`
              in_state c.recv p);
    reshuffle ();
    frame (fun _ -> gather_r c.recv vr) _;
    h_assert ((pts_to c.recv full vr `star` in_state_hprop p vr) `star`
               (chan_inv_step vr vs `star` (pts_to c.send half vs `star` trace_until c.trace vr)));
    h_commute _ _;
    h_assert (chan_inv_step vr vs `star`
              (pts_to c.send half vs `star` trace_until c.trace vr) `star`
              (pts_to c.recv full vr `star` in_state_hprop p vr));
    assoc_r _ _ _;
    let tok_chan_inv_step_p : squash (chan_inv_step_p vr vs)
      = frame (fun _ -> elim_pure #(chan_inv_step_p vr vs)) _ in
    assert (vs.chan_prot == step vr.chan_prot vr.chan_msg);
    h_elim_emp_l _;
    h_assert (((pts_to c.send half vs `star` trace_until c.trace vr) `star` (pts_to c.recv full vr `star` in_state_hprop p vr)));
    assoc_l _ _ _;
    frame_l (fun _ -> elim_pure #(in_state_prop p vr)) _;
    assert (vs.chan_prot == p);
    let s : squash (in_state_prop (step p vs.chan_msg) vs) = () in
    h_commute _ _;
    h_elim_emp_l _;
    h_assert ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full vr);
    intro_pure_p s _;
    h_assert (in_state_hprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full vr));
    frame_l (fun _ -> frame_l (fun _ -> write c.recv vs) _) _;
    h_assert (in_state_hprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full vs));
    frame_l (fun _ -> frame_l (fun _ -> share c.recv) _) _;
    h_assert (in_state_hprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star`
               (pts_to c.recv half vs `star` pts_to c.recv half vs)));
    reshuffle ();
    let next_p = step p vs.chan_msg in
    h_assert  ((pts_to c.recv half vs `star` in_state_hprop next_p vs) `star`
                ((pts_to c.send half vs `star` pts_to c.recv half vs) `star`
                  trace_until c.trace vr));
    frame (fun _ -> intro_h_exists vs
                 (fun (vs:chan_val) -> (pts_to c.recv half vs `star` in_state_hprop next_p vs))) _;
    h_assert (receiver cc next_p `star` ((pts_to c.send half vs `star` pts_to c.recv half vs) `star` trace_until c.trace vr));
    frame_l (fun _ -> frame_l (fun _ -> update_trace c.trace vr vs tok_chan_inv_step_p) _) _;
    h_assert (receiver cc next_p `star` ((pts_to c.send half vs `star` pts_to c.recv half vs) `star` trace_until c.trace vs));
    h_commute _ _;
    frame (fun _ -> intro_chan_inv c vs) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    return #_ #(fun x -> receiver cc (step p x)) vs.chan_msg

let send_pre_blocked (p:sprot) #q (c:chan_t q)  = sender_ahead c.send p c

let send_blocked (#p:prot{more p}) #q (cc:chan q) (x:msg_t p) (vs vr:chan_val)
                 (loop:(unit ->SteelT unit (sender cc p) (fun _ -> sender cc (step p x))))
                 (_:unit)
  : SteelT unit (send_pre_blocked p cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = let c = cc.chan_chan in
    h_assert ((pts_to c.send half vs `star`
               pts_to c.recv half vr `star`
               trace_until c.trace vr `star`
               chan_inv_step vr vs) `star`
               sender cc p);
    frame (fun _ -> intro_chan_inv_step c vs vr) _;
    h_assert (chan_inv c `star` sender cc p);
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    loop ()

let send_receive_prelude (#p:prot) (cc:chan p)
  : SteelT (chan_val & chan_val)
           emp
           (fun v ->
             pts_to cc.chan_chan.send half (fst v) `star`
             pts_to cc.chan_chan.recv half (snd v) `star`
             trace_until cc.chan_chan.trace (snd v) `star`
             chan_inv_cond (fst v) (snd v))
  = let c : chan_t p = cc.chan_chan in
    let l : lock (chan_inv c) = cc.chan_lock in
    let _ = acquire l in
    h_assert (chan_inv c);
    let vs = read_refine (chan_inv_recv c) c.send in
    h_assert (pts_to c.send half vs `star` chan_inv_recv c vs);
    h_commute _ _;
    frame (fun _ -> h_exists_assoc_r _ _ _) _;
    let vr = frame (fun _ -> read_refine (fun vr -> trace_until c.trace vr `star` chan_inv_cond vs vr) c.recv) _ in
    h_assert ((pts_to c.recv half vr `star` (trace_until c.trace vr `star` chan_inv_cond vs vr)) `star` pts_to c.send half vs);
    reshuffle ();
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star` trace_until c.trace vr `star` chan_inv_cond vs vr);
    let result : chan_val & chan_val = vs, vr in
    return #(chan_val & chan_val)
           #(fun result ->
              pts_to c.send half (fst result) `star`
              pts_to c.recv half (snd result) `star`
              trace_until cc.chan_chan.trace (snd result) `star`
              chan_inv_cond (fst result) (snd result))
           result

// let rec send (#p:prot{more p}) (c:chan) (x:msg_t p)
//  : Steel unit
//    (expects sender c p)
//    (provides fun _ -> sender c (step p x))
//  = acquire c.inv;
//    let _, _, n0 = !c.chan.send in
//    let _, _, n1 = !c.chan.recv in
//    if n0 == n1 //last send received
//    then (c.chan.send := (p, x, n0 + 1);
//          release c.inv)
//    else (release c.inv; send c x) //spin
let rec send (#q:prot) (cc:chan q) (#p:prot{more p}) (x:msg_t p)
  : SteelT unit (sender cc p) (fun _ -> sender cc (step p x))
  = h_assert (in_state cc.chan_chan.send p);
    h_intro_emp_l _;
    h_assert (emp `star` (in_state cc.chan_chan.send p));
    let v = frame (fun _ -> send_receive_prelude #q cc) _ in
    let vs = fst v in
    let vr = snd v in
    h_assert ((pts_to cc.chan_chan.send half vs `star`
               pts_to cc.chan_chan.recv half vr `star`
               trace_until cc.chan_chan.trace vr `star`
               chan_inv_cond vs vr) `star` (in_state cc.chan_chan.send p));
    h_assert (send_pre cc.chan_chan.send p cc.chan_chan vs vr);
    channel_cases cc.chan_chan.send #p cc x vs vr
                  (send_available #p cc x vs vr)
                  (send_blocked #p cc x vs vr (fun _ -> send cc x))


// let rec recv (#p:prot{more_msgs p}) (c:chan)
//   : Steel (msg_t p)
//     (expects receiver c p)
//     (provides fun x -> receiver v (step p x))
//   = acquire c.inv;
//     let qs, x, n0 = !i.chan.send in
//     let qr, y, n1 = !i.chan.recv in
//     if n0==n1 //last send already received
//     then (release i.inv; recv c)
//     else (c.chan.recv := (qs, x, n0);
//           release c.inv; x)


let channel_cases_recv
                  (r:ref chan_val) (#p:prot{more p}) #q (c:chan q) (vs vr:chan_val)
                  (then_: (unit -> SteelT (msg_t p) (send_recv_in_sync r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
                  (else_: (unit -> SteelT (msg_t p) (sender_ahead r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
    : SteelT (msg_t p) (send_pre r p c.chan_chan vs vr) (fun x -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_


let recv_blocked (#p:prot{more p}) #q (cc:chan q) (vs vr:chan_val)
                 (loop:unit -> SteelT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x)))
                 (_:unit)
  : SteelT (msg_t p) (send_recv_in_sync cc.chan_chan.recv p cc.chan_chan vs vr) (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    frame (fun _ -> intro_chan_inv_eq c vs vr) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    loop ()

let rec recv #q (#p:prot{more p}) (cc:chan q)
  : SteelT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x))
  = h_intro_emp_l _;
    let vs_vr = frame (fun _ -> send_receive_prelude cc) _ in
    let vs = fst vs_vr in
    let vr = snd vs_vr in
    h_assert (send_pre cc.chan_chan.recv p cc.chan_chan vs vr);
    channel_cases_recv cc.chan_chan.recv #p cc vs vr (recv_blocked #p cc vs vr (fun _ -> recv cc))
                                                     (recv_available #p cc vs vr)

let history_p' (#p:prot) (t:partial_trace_of p) (s:partial_trace_of p) : prop =
  t `extended_to` s /\ True

let history_p (#p:prot) (t:partial_trace_of p) : stable_property extended_to =
  history_p' t

let history (#p:prot) (c:chan p) (t:partial_trace_of p) : hprop =
  pure (witnessed c.chan_chan.trace (history_p t))


let history_duplicable (#p:prot) (c:chan p) (t:partial_trace_of p)
  : SteelT unit (history c t) (fun _ -> history c t `star` history c t)
  = dup_pure _

let extension_until #p (previous:partial_trace_of p) (q:prot) =
  (t:partial_trace_of p{previous `extended_to` t /\ until t == q})

let recall_trace_ref #q (r:trace_ref q) (tr tr':partial_trace_of q)
  : SteelT (squash (history_p tr tr'))
           (pts_to_ref r full tr'  `star` pure (witnessed r (history_p tr)))
           (fun _ -> pts_to_ref r full tr')
  = recall #(partial_trace_of q) #full #extended_to #(history_p tr) r tr';
    h_assert (pts_to_ref r full tr' `star` pure (history_p tr tr'));
    let s : squash (history_p tr tr') = frame_l (fun _ -> elim_pure #(history_p tr tr')) _ in
    h_commute _ _;
    h_elim_emp_l _;
    s

let witness_trace_ref #q (r:trace_ref q) (tr:partial_trace_of q)
  : SteelT unit (pts_to_ref r full tr)
                (fun _ -> pts_to_ref r full tr `star` pure (witnessed r (history_p tr)))
  = witness #_ #full #extended_to r (history_p tr) tr ()

let extend_history #q (c:chan q) (tr:partial_trace_of q) (v:chan_val)
  : SteelT (extension_of tr)
           (pts_to c.chan_chan.recv half v `star`
            history c tr `star`
            trace_until c.chan_chan.trace v)
           (fun tr' -> pts_to c.chan_chan.recv half v `star`
                    history c tr' `star`
                    trace_until c.chan_chan.trace v `star`
                    pure (until tr' == step v.chan_prot v.chan_msg))
  = let tr' = frame_l (fun _ -> read_monotonic_ref c.chan_chan.trace) _ in
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr) `star`
              (pts_to_ref c.chan_chan.trace full tr' `star`
               pure (until tr' == step v.chan_prot v.chan_msg)));
    reshuffle ();
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (pts_to_ref c.chan_chan.trace full tr'  `star` history c tr));
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (pts_to_ref c.chan_chan.trace full tr'  `star` pure (witnessed c.chan_chan.trace (history_p tr))));
    let trref : trace_ref q = c.chan_chan.trace in
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (pts_to_ref trref full tr'  `star` pure (witnessed trref (history_p tr))));
    let tr_extension = frame_l (fun _ -> recall_trace_ref trref tr tr') _ in
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              pts_to_ref trref full tr');
    frame_l (fun _ -> witness_trace_ref trref tr') _;
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (pts_to_ref trref full tr' `star` history c tr'));
    reshuffle ();
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              (pts_to_ref trref full tr' `star` pure (until tr' == step v.chan_prot v.chan_msg)));
    frame_l (fun _ -> frame_l (fun _ -> dup_pure _) _) _;
    frame_l (fun _ -> assoc_l _ _ _) _;
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              ((pts_to_ref trref full tr' `star` pure (until tr' == step v.chan_prot v.chan_msg))
                `star`
                pure (until tr' == step v.chan_prot v.chan_msg)));
    frame_l (fun _ -> frame (fun _ -> intro_trace_until trref tr' v) _) _;
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              (trace_until c.chan_chan.trace v `star` pure (until tr' == step v.chan_prot v.chan_msg)));
    reshuffle ();
    return #(extension_of tr) #(fun tr' -> pts_to c.chan_chan.recv half v `star`
                                        history c tr' `star`
                                        trace_until c.chan_chan.trace v `star`
                                        pure (until tr' == step v.chan_prot v.chan_msg)) tr'

let prot_equals #q (cc:chan q) #p (vr:chan_val)
  : SteelT (squash (step vr.chan_prot vr.chan_msg == p))
           (pts_to cc.chan_chan.recv half vr `star` receiver cc p)
           (fun _ -> pts_to cc.chan_chan.recv half vr `star` receiver cc p)
  = let vr' = frame_l (fun _ -> ghost_read_refine _ cc.chan_chan.recv) _ in
    //this assert seems to be necessay
    h_assert (pts_to cc.chan_chan.recv half vr `star` (pts_to cc.chan_chan.recv half vr' `star` in_state_hprop p vr'));
    assoc_l _ _ _;
    pts_to_injective #chan_val #_ #_ cc.chan_chan.recv (Ghost.hide vr) vr' (fun (vr':Ghost.erased chan_val) -> in_state_hprop p vr');
    h_assert (pts_to cc.chan_chan.recv half vr `star` pts_to cc.chan_chan.recv half vr `star` in_state_hprop p vr);
    let s = frame_l (fun _ -> elim_intro_pure #(in_state_prop p vr)) _ in
    assoc_r _ _ _;
    h_assert (pts_to cc.chan_chan.recv half vr `star` (pts_to cc.chan_chan.recv half vr `star` in_state_hprop p vr));
    frame_l (fun _ -> intro_h_exists vr (fun (vr:chan_val) -> (pts_to cc.chan_chan.recv half vr `star` in_state_hprop p vr))) _;
    h_assert (pts_to cc.chan_chan.recv half vr `star` receiver cc p);
    s


let rewrite_eq_squash_tok #a (x:a) (y:a) ($tok:squash (x==y)) (p:a -> hprop)
  : SteelT unit (p x) (fun _ -> p y)
  = h_assert (p y)

let witness_trace_until #q (r:trace_ref q) (vr:chan_val)
  : SteelT (partial_trace_of q)
           (trace_until r vr)
           (fun tr -> trace_until r vr `star` pure (witnessed r (history_p tr)))
  = let tr = read_monotonic_ref r in
    //need this assert
    h_assert (pts_to_ref r full tr `star` pure (until tr == step vr.chan_prot vr.chan_msg));
    frame (fun _ -> witness_trace_ref r tr) _;
    frame (fun _ -> h_commute _ _) _;
    assoc_r _ _ _;
    frame_l (fun _ -> intro_trace_until r tr vr) _;
    h_commute _ _;
    h_assert (trace_until r vr `star` pure (witnessed r (history_p tr)));
    return #(partial_trace_of q) tr

let trace #q (cc:chan q)
  : SteelT (partial_trace_of q) emp (fun tr -> history cc tr)
  = let _ = send_receive_prelude cc in
    rearrange_for_get_trace _ _ _ _;
    let tr = frame (fun _ -> witness_trace_until cc.chan_chan.trace _) _ in
    rearrange_for_get_trace2 _ _ _ _ _;
    frame (fun _ -> intro_chan_inv_aux cc.chan_chan _ _) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    return tr

let extend_trace (#q:prot) (#p:prot) (cc:chan q) (tr:partial_trace_of q)
  : SteelT (extension_of tr)
           (receiver cc p `star` history cc tr)
           (fun t -> receiver cc p `star` history cc t `star` pure (until t == p))
  = h_intro_emp_l _;
    let vs_vr = frame (fun _ -> send_receive_prelude cc) _ in
    let vs = fst vs_vr in
    let vr = snd vs_vr in
    let c = cc.chan_chan in
    h_assert ((pts_to c.send half vs `star`
               pts_to c.recv half vr `star`
               trace_until c.trace vr `star`
               chan_inv_cond vs vr) `star`
              (receiver cc p `star` history cc tr));
    reshuffle ();
    h_assert ((pts_to c.recv half vr `star`
                history cc tr `star`
                trace_until c.trace vr) `star`
               (pts_to c.send half vs `star`
                (chan_inv_cond vs vr `star` receiver cc p)));
    let tr' = frame (fun _ -> extend_history cc tr vr) _ in
    h_assert ((pts_to c.recv half vr `star`
                history cc tr' `star`
                trace_until c.trace vr `star`
                pure (until tr' == step vr.chan_prot vr.chan_msg)) `star`
               (pts_to c.send half vs `star`
                (chan_inv_cond vs vr `star` receiver cc p)));
    reshuffle ();
    let tok = frame (fun _ -> prot_equals cc vr) _ in
    assert (step vr.chan_prot vr.chan_msg == p);
    rewrite_eq_squash_tok _ _ tok (fun zz ->
              ((pts_to c.recv half vr `star` receiver cc p) `star`
               (pure (until tr' == zz) `star`
                (history cc tr' `star`
                 trace_until c.trace vr `star`
                 pts_to c.send half vs `star`
                 chan_inv_cond vs vr))));
    reshuffle ();
    frame (fun _ -> intro_chan_inv_aux cc.chan_chan vs vr) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    h_assert (receiver cc p `star` (history cc tr' `star` pure (until tr' == p)));
    assoc_l _ _ _;
    return tr'
