(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.Channel.Simplex
module P = Steel.Channel.Protocol
open Steel.SpinLock
open Steel.Effect
open Steel.Memory
open Steel.HigherReference
module SX = Steel.EffectX
open Steel.SteelXT.Basics


module T = FStar.Tactics
module ST = Steel.Memory.Tactics


(* Some helpers *)
private
val reshuffle0 (#p #q : slprop)
              (_ : squash (p `equiv` q))
   : SX.SteelXT unit p (fun _ -> q)

private
let reshuffle0 #p #q peq =
  Steel.EffectX.Atomic.change_slprop p q (fun m -> ())

private
val reshuffle (#p #q : slprop)
              (_ : squash (T.with_tactic ST.canon
                                         (squash (p `equiv` q))))
   : SX.SteelXT unit p (fun _ -> q)

#push-options "--no_tactics" (* GM: This should not be needed *)

private
let reshuffle #p #q peq =
  T.by_tactic_seman ST.canon (squash (p `equiv` q));
  reshuffle0 ()

#pop-options

////////////////////////////////////////////////////////////////////////////////
// Some generic lemmas
////////////////////////////////////////////////////////////////////////////////
let assoc_r (p q r:slprop)
  : SX.SteelXT unit ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = reshuffle ()

let assoc_l (p q r:slprop)
  : SX.SteelXT unit (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = reshuffle ()

let pts_to_injective #a #p #q (r:ref a) (v0 v1:Ghost.erased a) (rest:Ghost.erased a -> slprop)
  : SX.SteelXT unit (pts_to r p v0 `star` pts_to r q v1 `star` rest v1)
                (fun _ -> pts_to r p v0 `star` pts_to r q v0 `star` rest v0)
  = Steel.EffectX.Atomic.change_slprop _ _
                (fun m -> pts_to_ref_injective r p q v0 v1 m;
                       assert (v0 == v1))

open Steel.FractionalPermission

(* Since pts_to is witness-invariant, we can witness any `q` here. *)
let ghost_read_refine (#a:Type) (#p:perm) (q:a -> slprop) (r:ref a)
  : SX.SteelXT (Ghost.erased a) (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = pts_to_witinv r p;
    star_is_witinv_left (fun (v:a) -> pts_to r p v) q;
    witness_h_exists ()

val intro_pure_p (#p:prop) (s:squash p) (h:slprop)
  : SX.SteelXT unit h (fun _ -> pure p `star` h)
let intro_pure_p #p s h = intro_pure p; h_commute _ _

val elim_pure (#p:prop)
  : SX.SteelXT (squash p) (pure p) (fun _ -> emp)
let elim_pure #p =
  assert (exists m. interp (pure p) m);
  FStar.Classical.forall_intro (pure_star_interp emp p);
  reshuffle ();
  h_affine emp (pure p);
  ()

val intro_pure (#p:prop) (s:squash p)
  : SX.SteelXT unit emp (fun _ -> pure p)
let intro_pure #p s =
  intro_pure_p #p s emp;
  reshuffle ()

let elim_intro_pure (#p:prop)
  : SX.SteelXT (squash p) (pure p) (fun _ -> pure p)
  = let s = elim_pure #p in
    intro_pure #p s;
    s

let dup_pure (p:prop)
  : SX.SteelXT unit (pure p) (fun _ -> pure p `star` pure p)
  = let s = elim_intro_pure #p in
    intro_pure_p s _

let rewrite_ext (p q:slprop) (_:squash (p == q))
  : SX.SteelXT unit p (fun _ -> q)
  = return ()

let h_exists_assoc_r (#a:Type) (p q r: a -> slprop)
  : SX.SteelXT unit (h_exists (fun x -> p x `star` q x `star` r x))
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

let rearrange_for_get_trace2 (p q r s t : slprop)
  : SX.SteelXT unit ((p `star` q) `star` (r `star` s `star` t))
                (fun _ -> (r `star` s `star` p `star` t) `star` q)
  = reshuffle ()


let rearrange_for_get_trace (p q r s : slprop)
  : SX.SteelXT unit (p `star` q `star` r `star` s)
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

module MRef = Steel.MonotonicHigherReference
let mref a p = MRef.ref a p
let trace_ref (p:prot) = mref (partial_trace_of p) extended_to

noeq
type chan_t (p:prot) = {
  send: ref chan_val;
  recv: ref chan_val;
  trace: trace_ref p;
}

let half : perm = half_perm full_perm

let step (s:sprot) (x:msg_t s) = step s x

let chan_inv_step_p (vrecv vsend:chan_val) : prop =
  (vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg /\
   vsend.chan_ctr == vrecv.chan_ctr + 1)

let chan_inv_step (vrecv vsend:chan_val) : slprop =
  pure (chan_inv_step_p vrecv vsend)

let chan_inv_cond (vsend:chan_val) (vrecv:chan_val) : slprop =
    if vsend.chan_ctr = vrecv.chan_ctr
    then pure (vsend == vrecv)
    else chan_inv_step vrecv vsend

let trace_until_prop #p (r:trace_ref p) (vr:chan_val) (tr: partial_trace_of p) : slprop =
  MRef.pts_to r full_perm tr `star`
  pure (until tr == step vr.chan_prot vr.chan_msg)

let trace_until #p (r:trace_ref p) (vr:chan_val) =
  h_exists (trace_until_prop r vr)

let chan_inv_recv #p (c:chan_t p) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star`
      trace_until c.trace vrecv `star`
      chan_inv_cond vsend vrecv)

let chan_inv #p (c:chan_t p) : slprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

let rewrite_eq_squash #a (x:a) (y:a{x==y}) (p:a -> slprop)
  : SX.SteelXT unit (p x) (fun _ -> p y)
  = h_assert (p y)

let intro_chan_inv_cond_eq (vs vr:chan_val)
  : SX.SteelXT unit (pure (vs == vr))
                (fun _ -> chan_inv_cond vs vr)
  = elim_pure #(vs==vr);
    assert (vs == vr);
    intro_pure #(vs == vs) ();
    h_assert (chan_inv_cond vs vs);
    rewrite_eq_squash vs vr (chan_inv_cond vs);
    h_assert (chan_inv_cond vs vr)

let intro_chan_inv_cond_step (vs vr:chan_val)
  : SX.SteelXT unit (chan_inv_step vr vs)
                (fun _ -> chan_inv_cond vs vr)
  = elim_intro_pure #(chan_inv_step_p vr vs);
    assert (chan_inv_step_p vr vs);
    h_assert (chan_inv_step vr vs);
    rewrite_ext (chan_inv_step vr vs) (chan_inv_cond vs vr) ()

let frame_l #a #q #r (f:unit -> SX.SteelXT a q r) (p:slprop)
  : SX.SteelXT a (p `star` q) (fun x -> p `star` r x)
  = h_commute _ _;
    let x = frame f _ in
    h_commute _ _;
    return x

let intro_chan_inv_aux #p (c:chan_t p) (vs vr:chan_val)
  : SX.SteelXT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_cond vs vr)
                 (fun _ -> chan_inv c)
  = reshuffle ();
    frame (fun _ -> intro_h_exists vr (fun (vr:chan_val) -> pts_to c.recv half vr `star` trace_until c.trace vr `star` chan_inv_cond vs vr)) (pts_to c.send half vs);
    h_commute _ _;
    intro_h_exists vs _

let intro_chan_inv_step #p (c:chan_t p) (vs vr:chan_val)
  : SX.SteelXT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_step vr vs)
                 (fun _ -> chan_inv c)
  = frame_l (fun _ -> intro_chan_inv_cond_step vs vr) _;
    intro_chan_inv_aux c vs vr

let intro_chan_inv_eq #p (c:chan_t p) (vs vr:chan_val)
  : SX.SteelXT unit (pts_to c.send half vs `star`
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

let in_state_slprop (p:prot) (vsend:chan_val) : slprop = pure (in_state_prop p vsend)

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pts_to r half vsend `star` in_state_slprop p vsend)

let sender #q (c:chan q) (p:prot) = in_state c.chan_chan.send p
let receiver #q (c:chan q) (p:prot) = in_state c.chan_chan.recv p

let intro_chan_inv #p (c:chan_t p) (v:chan_val)
  : SX.SteelXT unit (pts_to c.send half v `star`
                 pts_to c.recv half v `star`
                 trace_until c.trace v)
                (fun _ -> chan_inv c)
  = intro_pure_p #(v==v) () _;
    h_commute _ _;
    intro_chan_inv_eq c v v

let chan_val_p (p:prot) = (vs0:chan_val { in_state_prop p vs0 })

let intro_in_state (r:ref chan_val) (p:prot) (v:chan_val_p p)
  : SX.SteelXT unit (pts_to r half v) (fun _ -> in_state r p)
  = intro_pure_p #(in_state_prop p v) () _;
    h_commute _ _;
    intro_h_exists v _

let eq #a (x y : a) :prop = x == y

let rewrite_eq #a (x:a) (y:a) (p:a -> slprop)
  : SX.SteelXT unit (pure (eq x y) `star` p x) (fun _ -> p y)
  = let _ = frame (fun _ -> elim_pure #(eq x y)) (p x) in
    h_assert (emp `star` p x);
    h_commute _ _;
    h_affine _ _;
    h_assert (p x);
    assert (x == y);
    rewrite_eq_squash x y p

#push-options "--print_universes"



let mk_chan_t_val (#p:prot) (send recv:ref chan_val) (tr:trace_ref p)
  : SX.SteelXT (c:chan_t p{c==Mkchan_t send recv tr}) emp (fun c -> emp)
  = let c = (Mkchan_t send recv tr) in
    return #_ #(fun c -> emp) c

let msg t p = Msg Send unit (fun _ -> p)
let init_chan_val (p:prot) = v:chan_val {v.chan_prot == msg unit p}

let initial_trace (p:prot) : (q:partial_trace_of p {until q == p})
  = { to = p; tr=Waiting p}

let intro_until_eq #p (c:chan_t p) (v:init_chan_val p) //{p == step v.chan_prot v.chan_msg})
  : SX.SteelXT unit emp (fun _ -> pure (until (initial_trace p) == (step v.chan_prot v.chan_msg)))
  = let s :squash (until (initial_trace p) == (step v.chan_prot v.chan_msg)) = () in
    intro_pure #_ s

let intro_trace_until #q (r:trace_ref q) (tr:partial_trace_of q) (v:chan_val)
  : SX.SteelXT unit (MRef.pts_to r full_perm tr `star` pure (until tr == step v.chan_prot v.chan_msg))
                (fun _ -> trace_until r v)
  = intro_h_exists tr
                (fun (tr:partial_trace_of q) ->
                     MRef.pts_to r full_perm tr `star`
                     pure (until tr == (step v.chan_prot v.chan_msg)))

let intro_trace_untilT #q (r:trace_ref q) (tr:partial_trace_of q) (v:chan_val)
  : SteelT unit (MRef.pts_to r full_perm tr `star` pure (until tr == step v.chan_prot v.chan_msg))
                (fun _ -> trace_until r v)
  = intro_trace_until r tr v

let intro_trace_until_init  #p (c:chan_t p) (v:init_chan_val p)
  : SX.SteelXT unit (MRef.pts_to c.trace full_perm (initial_trace p))
                (fun _ -> trace_until c.trace v)
  = h_intro_emp_l _;
    frame (fun _ -> intro_until_eq c v) _;
    h_assert (pure (until (initial_trace p) == (step v.chan_prot v.chan_msg)) `star`
              MRef.pts_to c.trace full_perm (initial_trace p));
    reshuffle ();
    intro_trace_until c.trace (initial_trace p) v

let chan_t_sr (p:prot) (send recv:ref chan_val) = (c:chan_t p{c.send == send /\ c.recv == recv})

let rearrange_pqr_qrp (p q r:slprop)
  : SX.SteelXT unit (p `star` (q `star` r))
                (fun _ -> q `star` r `star` p)
  = reshuffle ()

let alloc_mref (#a:Type) (p:Preorder.preorder a) (v:a)
  : SX.SteelXT (MRef.ref a p) emp (fun r -> MRef.pts_to r full_perm v)
  = as_steelx (fun _ -> MRef.alloc p v)

let mk_chan_t (#p:prot) (send recv:ref chan_val) (v:init_chan_val p)
  : SX.SteelXT (chan_t_sr p send recv)
           (pts_to send half v `star` pts_to recv half v)
           (fun c -> chan_inv c)
  = h_intro_emp_l _;
    let tr : trace_ref p = frame (fun _ -> alloc_mref (extended_to #p) (initial_trace p)) _ in
    h_assert (MRef.pts_to tr full_perm (initial_trace p) `star` (pts_to send half v `star` pts_to recv half v));
    h_intro_emp_l _;
    let c = frame (fun _ -> mk_chan_t_val #p send recv tr) _ in
    h_elim_emp_l _;
    h_assert ((MRef.pts_to c.trace full_perm (initial_trace p) `star` (pts_to c.send half v `star` pts_to c.recv half v)));
    frame (fun _ -> intro_trace_until_init c v) _;
    h_assert (trace_until c.trace v `star` (pts_to c.send half v `star` pts_to c.recv half v));
    reshuffle #_
              #(pts_to c.send half v `star` pts_to c.recv half v `star` trace_until c.trace v)
              ();
    h_assert (pts_to c.send half v `star` pts_to c.recv half v `star` trace_until c.trace v);
    intro_chan_inv c v;
    let c' : chan_t_sr p send recv = c in
    return #(chan_t_sr p send recv) #(fun c -> chan_inv c) c'

let alloc (#a:Type) (x:a)
  : SX.SteelXT (ref a) emp (fun r -> pts_to r full_perm x)
  = as_steelx (fun _ -> alloc x)

let share_x (#a:Type) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SX.SteelXT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = as_steelx (fun _ -> share r)

let new_lock (p:slprop)
  : SX.SteelXT (lock p) p (fun _ -> emp)
  = as_steelx (fun _ -> new_lock p)

let new_chan_x (p:prot)
  : SX.SteelXT (chan p) emp (fun c -> sender c p `star` receiver c p)
  = let q = msg unit p in
    let v : chan_val = { chan_prot = q; chan_msg = (); chan_ctr = 0 } in
    let vp : init_chan_val p = v in
    let send = alloc v in
    h_assert (pts_to send full_perm v);
    h_intro_emp_l (pts_to send full_perm v);
    let recv = frame (fun _ -> alloc v) _ in //(pts_to send full v) in
    h_assert (pts_to recv full_perm v `star` pts_to send full_perm v);
    let _  = frame (fun _ -> share_x recv) _ in //(pts_to send full_perm v) in
    h_assert ((pts_to recv half v `star` pts_to recv half v) `star` pts_to send full_perm v);
    h_commute _ _;
    let _  = frame (fun _ -> share_x send) _ in
    h_assert ((pts_to send half v `star` pts_to send half v) `star`
              (pts_to recv half v `star` pts_to recv half v));
    reshuffle #_ #((pts_to send half v `star` pts_to recv half v) `star` (pts_to send half v `star` pts_to recv half v)) ();
    let c : chan_t_sr p send recv = frame (fun _ -> mk_chan_t #p send recv vp) _ in
    h_assert (chan_inv c `star` (pts_to send half v `star` pts_to recv half v));
    reshuffle #_ #(pts_to send half v `star` (pts_to recv half v `star` chan_inv c)) ();
    h_assert (pts_to send half v `star` (pts_to recv half v `star` chan_inv c));
    let vp : chan_val_p p = v in
    h_assert (pts_to send half vp `star` (pts_to recv half vp `star` chan_inv c));
    frame (fun _ -> intro_in_state send p vp) _; //(pts_to recv half v `star` chan_inv c) in
    h_assert (in_state send p `star` (pts_to recv half v `star` chan_inv c));
    reshuffle #_ #(pts_to recv half v `star` (chan_inv c `star` in_state send p)) ();
    let _ = frame (fun _ -> intro_in_state recv p vp) _ in
    h_assert (in_state recv p `star` (chan_inv c `star` in_state send p));
    reshuffle #_ #((chan_inv c `star` (in_state send p `star` in_state recv p))) ();
    h_assert (chan_inv c `star` (in_state send p `star` in_state recv p));
    let l : lock (chan_inv c) = frame (fun _ -> new_lock (chan_inv c)) _ in
    let ch : chan p = { chan_chan = c; chan_lock = l } in
    h_assert (emp `star` (in_state send p `star` in_state recv p));
    reshuffle #_ #((in_state send p `star` in_state recv p)) ();
    rewrite_eq_squash send ch.chan_chan.send (fun s -> in_state s p `star` in_state recv p);
    rewrite_eq_squash recv ch.chan_chan.recv (fun r -> in_state ch.chan_chan.send p `star` in_state r p);
    h_assert (sender ch p `star` receiver ch p);
    return #(chan p) #(fun ch -> (sender ch p `star` receiver ch p)) ch

let new_chan (p:prot) : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)
  = new_chan_x p

let send_pre (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val) : slprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   trace_until c.trace vr `star`
   chan_inv_cond vs vr `star`
   in_state r p)

let send_pre_split (r:ref chan_val)  (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val) (b:bool) : slprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   trace_until c.trace vr `star`
   (if b then pure (vs == vr) else chan_inv_step vr vs) `star`
   in_state r p)

let send_recv_in_sync (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : slprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     pure (vs == vr) `star`
     in_state r p)

let sender_ahead (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : slprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     chan_inv_step vr vs `star`
     in_state r p)

let channel_cases (r:ref chan_val) (#p:prot{more p}) #q (c:chan q) (x:msg_t p) (vs vr:chan_val)
                  (then_: (unit -> SX.SteelXT unit (send_recv_in_sync r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
                  (else_: (unit -> SX.SteelXT unit (sender_ahead r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
    : SX.SteelXT unit (send_pre r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      SX.cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_

let gather (#a:Type) (#v0 #v1:Ghost.erased a) (r:ref a)
  : SX.SteelXT unit
    (pts_to r half v0 `star` pts_to r half v1)
    (fun _ -> pts_to r full_perm v0)
  = as_steelx (fun _ -> gather r)

let share (#a:Type) (#v:a) (r:ref a)
  : SX.SteelXT unit
    (pts_to r full_perm v)
    (fun _ -> pts_to r half v `star` pts_to r half v)
  = as_steelx (fun _ -> share r)

let update_channel (#p:sprot) #q (c:chan_t q) (x:msg_t p) (vs:chan_val) (r:ref chan_val)
  : SX.SteelXT chan_val
           (pts_to r full_perm vs `star` in_state_slprop p vs)
           (fun vs' -> pts_to r full_perm vs' `star` (in_state_slprop (step p x) vs' `star` chan_inv_step vs vs'))
  = h_commute _ _;
    frame (fun _ -> elim_pure #(in_state_prop p vs)) _;
    h_elim_emp_l _;
    let vs' = next_chan_val x vs in
    as_steelx (fun _ -> write r vs');
    intro_pure_p #(in_state_prop (step p x) vs') () _;
    h_commute _ _;
    h_assert (pts_to r full_perm vs' `star` in_state_slprop (step p x) vs');
    intro_pure_p #(chan_inv_step_p vs vs') () _;
    h_assert (chan_inv_step vs vs' `star` (pts_to r full_perm vs' `star` in_state_slprop (step p x) vs'));
    reshuffle #_ #((pts_to r full_perm vs' `star` (in_state_slprop (step p x) vs' `star` chan_inv_step vs vs'))) ();
    h_assert (pts_to r full_perm vs' `star` (in_state_slprop (step p x) vs' `star` chan_inv_step vs vs'));
    return #chan_val #(fun vs' -> pts_to r full_perm vs' `star` (in_state_slprop (step p x) vs' `star` chan_inv_step vs vs')) vs'

let send_pre_available (p:sprot) #q (c:chan_t q) (vs vr:chan_val)  = send_recv_in_sync c.send p c vs vr

let gather_r (#p:sprot) (r:ref chan_val) (v:chan_val)
  : SX.SteelXT unit
    (pts_to r half v `star` in_state r p)
    (fun _ -> pts_to r full_perm v `star` in_state_slprop p v)
  = h_commute _ _;
    h_assert (in_state r p `star` pts_to r half v);
    let sub () : SX.SteelXT _ _ _ = ghost_read_refine (in_state_slprop p) r in
    let v' = frame sub _ in
    h_assert ((pts_to r half v' `star` in_state_slprop p v') `star` pts_to r half v);
    reshuffle #_ #(((pts_to r half v `star` pts_to r half v') `star` in_state_slprop p v')) ();
    h_assert ((pts_to r half v `star` pts_to r half v') `star` in_state_slprop p v');
    pts_to_injective #_ #half #half r (Ghost.hide v) v' (fun (v':Ghost.erased chan_val) -> in_state_slprop p v');
    h_assert (pts_to r half v `star` pts_to r half v `star` in_state_slprop p v);
    frame (fun _ -> gather r) _

let release (#p:slprop) (l:lock p)
  : SX.SteelXT unit p (fun _ -> emp)
  = as_steelx (fun _ -> release l)

let send_available (#p:sprot) #q (cc:chan q) (x:msg_t p) (vs vr:chan_val) (_:unit)
  : SX.SteelXT unit (send_pre_available p #q cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = let c : chan_t q = cc.chan_chan in
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star`
              trace_until c.trace vr `star`
              pure (vs == vr) `star`
              in_state c.send p);
    reshuffle #_
              #((pure (vs == vr) `star` (
                         pts_to c.send half vs `star`
                         pts_to c.recv half vr `star`
                         trace_until c.trace vr `star`
                         in_state c.send p))) ();
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
    reshuffle #_ #(((pts_to c.send half vs `star` in_state c.send p) `star`
                    (pts_to c.recv half vs `star` trace_until c.trace vs))) ();
    h_assert ((pts_to c.send half vs `star` in_state c.send p) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    frame (fun _ -> gather_r c.send vs) _;
    h_assert ((pts_to c.send full_perm vs `star` in_state_slprop p vs) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    let next_vs = frame (fun _ -> update_channel c x vs c.send) _ in
    h_assert ((pts_to c.send full_perm next_vs `star` (in_state_slprop (step p x) next_vs `star` chan_inv_step vs next_vs)) `star`
              (pts_to c.recv half vs `star` trace_until c.trace vs));
    assoc_r _ _ _;
    frame (fun _ -> share #_ #next_vs c.send) _;
    reshuffle #((pts_to c.send half next_vs `star` pts_to c.send half next_vs) `star`
               ((in_state_slprop (step p x) next_vs `star` chan_inv_step vs next_vs) `star`
                (pts_to c.recv half vs `star` trace_until c.trace vs)))
              #((pts_to c.send half next_vs `star` in_state_slprop (step p x) next_vs) `star`
                ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                  (pts_to c.recv half vs `star` trace_until c.trace vs)))
              ();
    frame (fun _ -> intro_h_exists next_vs (fun (next_vs:chan_val) -> pts_to c.send half next_vs `star` in_state_slprop (step p x) next_vs)) _;
    h_assert (sender cc (step p x) `star`
               ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                 (pts_to c.recv half vs `star` trace_until c.trace vs)));
    reshuffle #_ #((pts_to c.send half next_vs `star`
                          pts_to c.recv half vs `star`
                          trace_until c.trace vs `star`
                          chan_inv_step vs next_vs) `star`
                   sender cc (step p x)) ();
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
  : squash (chan_inv_step_p vr vs)
  = ()

let next_trace_st #p (vr:chan_val) (vs:chan_val) (tr:partial_trace_of p)
  : SX.SteelXT (extension_of tr)
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

let write_mref_x (#a:Type) (#p:Preorder.preorder a) (#v:Ghost.erased a)
          (r:MRef.ref a p) (x:a{p v x})
  : SX.SteelXT unit (MRef.pts_to r full_perm v)
                (fun v -> MRef.pts_to r full_perm x)
  = as_steelx (fun _ -> MRef.write r x)

let write_trace #p (r:trace_ref p)
                   (old_tr:partial_trace_of p)
                   (new_tr:extension_of old_tr)
  : SX.SteelXT unit (MRef.pts_to r full_perm old_tr)
                (fun _ -> MRef.pts_to r full_perm new_tr)
  = let _ = write_mref_x #_ #_ #old_tr r new_tr in
    return ()

let trace_property #p (vr:chan_val) (tr:partial_trace_of p) : slprop =
  pure (eq (until tr) (step vr.chan_prot vr.chan_msg))

let update_trace #p (r:trace_ref p) (vr:chan_val) (vs:chan_val) (s:squash (chan_inv_step_p vr vs))
  : SX.SteelXT unit
           (trace_until r vr) // `star` chan_inv_step vr vs)
           (fun _ -> trace_until r vs)
  = intro_pure_p s _;
    h_commute _ _;
    h_assert ((h_exists (fun (tr:partial_trace_of p) ->
                   MRef.pts_to r full_perm tr `star`
                   pure (until tr == step vr.chan_prot vr.chan_msg))) `star`
               chan_inv_step vr vs);
    let sub () : SX.SteelXT _ _ _
       = as_steelx (fun _ ->
         MRef.read_refine #(partial_trace_of p) #full_perm #(extended_to)
           #(trace_property vr)
           r)
    in
    let tr = frame sub _ in
    h_assert ((MRef.pts_to r full_perm tr `star` pure (eq (until tr) (step vr.chan_prot vr.chan_msg))) `star` chan_inv_step vr vs);
    assoc_r _ _ _;
    frame_l (fun _ -> h_commute _ _) _;
    let ts : extension_of tr = frame_l (fun _ -> next_trace_st vr vs tr) _ in
    h_assert (MRef.pts_to r full_perm tr `star` pure (until ts == step vs.chan_prot vs.chan_msg));
    frame (fun _ -> write_trace r tr ts) _;
    h_assert (MRef.pts_to r full_perm ts `star` pure (until ts == step vs.chan_prot vs.chan_msg));
    intro_h_exists ts (fun (ts:partial_trace_of p) ->
                         MRef.pts_to r full_perm ts `star`
                         pure (until ts == step vs.chan_prot vs.chan_msg))

let write (#a:Type) (#v:Ghost.erased a) (r:ref a) (x:a)
  : SX.SteelXT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)
  = as_steelx (fun _ -> write r x)

let recv_available (#p:sprot) #q (cc:chan q) (vs vr:chan_val) (_:unit)
  : SX.SteelXT (msg_t p)
    (sender_ahead cc.chan_chan.recv p cc.chan_chan vs vr)
    (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star`
              trace_until c.trace vr `star`
              chan_inv_step vr vs `star`
              in_state c.recv p);
    reshuffle #_ #((pts_to c.recv half vr `star` in_state c.recv p) `star` _) ();
    frame (fun _ -> gather_r c.recv vr) _;
    h_assert ((pts_to c.recv full_perm vr `star` in_state_slprop p vr) `star`
               (chan_inv_step vr vs `star` (pts_to c.send half vs `star` trace_until c.trace vr)));
    h_commute _ _;
    h_assert (chan_inv_step vr vs `star`
              (pts_to c.send half vs `star` trace_until c.trace vr) `star`
              (pts_to c.recv full_perm vr `star` in_state_slprop p vr));
    assoc_r _ _ _;
    let tok_chan_inv_step_p : squash (chan_inv_step_p vr vs)
      = frame (fun _ -> elim_pure #(chan_inv_step_p vr vs)) _ in
    assert (vs.chan_prot == step vr.chan_prot vr.chan_msg);
    h_elim_emp_l _;
    h_assert (((pts_to c.send half vs `star` trace_until c.trace vr) `star` (pts_to c.recv full_perm vr `star` in_state_slprop p vr)));
    assoc_l _ _ _;
    frame_l (fun _ -> elim_pure #(in_state_prop p vr)) _;
    assert (vs.chan_prot == p);
    let s : squash (in_state_prop (step p vs.chan_msg) vs) = () in
    h_commute _ _;
    h_elim_emp_l _;
    h_assert ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full_perm vr);
    intro_pure_p s _;
    h_assert (in_state_slprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full_perm vr));
    frame_l (fun _ -> frame_l (fun _ -> write c.recv vs) _) _;
    h_assert (in_state_slprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star` pts_to c.recv full_perm vs));
    frame_l (fun _ -> frame_l (fun _ -> share c.recv) _) _;
    h_assert (in_state_slprop (step p vs.chan_msg) vs `star`
              ((pts_to c.send half vs `star` trace_until c.trace vr) `star`
               (pts_to c.recv half vs `star` pts_to c.recv half vs)));
    reshuffle #_ #(((pts_to c.recv half vs `star` in_state_slprop (step p vs.chan_msg) vs) `star`
                ((pts_to c.send half vs `star` pts_to c.recv half vs) `star`
                  trace_until c.trace vr))) ();
    let next_p = step p vs.chan_msg in
    h_assert  ((pts_to c.recv half vs `star` in_state_slprop next_p vs) `star`
                ((pts_to c.send half vs `star` pts_to c.recv half vs) `star`
                  trace_until c.trace vr));
    frame (fun _ -> intro_h_exists vs
                 (fun (vs:chan_val) -> (pts_to c.recv half vs `star` in_state_slprop next_p vs))) _;
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
                 (loop:(unit -> SX.SteelXT unit (sender cc p) (fun _ -> sender cc (step p x))))
                 (_:unit)
  : SX.SteelXT unit (send_pre_blocked p cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
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

let send_receive_prelude_x (#p:prot) (cc:chan p)
  : SX.SteelXT (chan_val & chan_val)
           emp
           (fun v ->
             pts_to cc.chan_chan.send half (fst v) `star`
             pts_to cc.chan_chan.recv half (snd v) `star`
             trace_until cc.chan_chan.trace (snd v) `star`
             chan_inv_cond (fst v) (snd v))
  = let c : chan_t p = cc.chan_chan in
    let l : lock (chan_inv c) = cc.chan_lock in
    let _ = as_steelx (fun _ -> acquire l) in
    h_assert (chan_inv c);
    let vs = as_steelx (fun _ -> read_refine (chan_inv_recv c) c.send) in
    h_assert (pts_to c.send half vs `star` chan_inv_recv c vs);
    h_commute _ _;
    frame (fun _ -> h_exists_assoc_r _ _ _) _;
    let sub () : SX.SteelXT _ _ _ = as_steelx (fun _ -> read_refine (fun vr -> trace_until c.trace vr `star` chan_inv_cond vs vr) c.recv) in
    let vr = frame sub _ in
    h_assert ((pts_to c.recv half vr `star` (trace_until c.trace vr `star` chan_inv_cond vs vr)) `star` pts_to c.send half vs);
    reshuffle #_ #((pts_to c.send half vs `star`
              pts_to c.recv half vr `star` trace_until c.trace vr `star` chan_inv_cond vs vr)) ();
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

let send_receive_prelude (#p:prot) (cc:chan p)
  : SteelT (chan_val & chan_val)
           emp
           (fun v ->
             pts_to cc.chan_chan.send half (fst v) `star`
             pts_to cc.chan_chan.recv half (snd v) `star`
             trace_until cc.chan_chan.trace (snd v) `star`
             chan_inv_cond (fst v) (snd v))
  = let c = cc.chan_chan in
    Steel.SpinLock.acquire cc.chan_lock;
    let vs = read_refine (chan_inv_recv cc.chan_chan) cc.chan_chan.send in
    let _ = Steel.Effect.Atomic.witness_h_exists () in
    let vr = Steel.HigherReference.read cc.chan_chan.recv in
    Steel.Effect.change_slprop (trace_until _ _ `star` chan_inv_cond _ _)
                               (trace_until cc.chan_chan.trace vr `star` chan_inv_cond vs vr)
                               (fun _ -> ());
    (vs, vr)

let rec send_x (#q:prot) (cc:chan q) (#p:prot{more p}) (x:msg_t p)
  : SX.SteelXT unit (sender cc p) (fun _ -> sender cc (step p x))
  = h_assert (in_state cc.chan_chan.send p);
    h_intro_emp_l _;
    h_assert (emp `star` (in_state cc.chan_chan.send p));
    let v = frame (fun _ -> send_receive_prelude_x #q cc) _ in
    let vs = fst v in
    let vr = snd v in
    h_assert ((pts_to cc.chan_chan.send half vs `star`
               pts_to cc.chan_chan.recv half vr `star`
               trace_until cc.chan_chan.trace vr `star`
               chan_inv_cond vs vr) `star` (in_state cc.chan_chan.send p));
    h_assert (send_pre cc.chan_chan.send p cc.chan_chan vs vr);
    channel_cases cc.chan_chan.send #p cc x vs vr
                  (send_available #p cc x vs vr)
                  (send_blocked #p cc x vs vr (fun _ -> send_x cc x))

let send (#p:prot) (c:chan p) (#next:prot{more next}) (x:msg_t next)
  : SteelT unit (sender c next) (fun _ -> sender c (step next x))
  = send_x c x

let channel_cases_recv
                  (r:ref chan_val) (#p:prot{more p}) #q (c:chan q) (vs vr:chan_val)
                  (then_: (unit -> SX.SteelXT (msg_t p) (send_recv_in_sync r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
                  (else_: (unit -> SX.SteelXT (msg_t p) (sender_ahead r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
    : SX.SteelXT (msg_t p) (send_pre r p c.chan_chan vs vr) (fun x -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      SX.cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_

let recv_blocked (#p:prot{more p}) #q (cc:chan q) (vs vr:chan_val)
                 (loop:unit -> SX.SteelXT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x)))
                 (_:unit)
  : SX.SteelXT (msg_t p) (send_recv_in_sync cc.chan_chan.recv p cc.chan_chan vs vr) (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    frame (fun _ -> intro_chan_inv_eq c vs vr) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    loop ()

let rec recv_x #q (#p:prot{more p}) (cc:chan q)
  : SX.SteelXT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x))
  = h_intro_emp_l _;
    let vs_vr = frame (fun _ -> send_receive_prelude_x cc) _ in
    let vs = fst vs_vr in
    let vr = snd vs_vr in
    h_assert (send_pre cc.chan_chan.recv p cc.chan_chan vs vr);
    channel_cases_recv cc.chan_chan.recv #p cc vs vr (recv_blocked #p cc vs vr (fun _ -> recv_x cc))
                                                     (recv_available #p cc vs vr)

let recv (#p:prot) (#next:prot{more next}) (c:chan p)
  : SteelT (msg_t next) (receiver c next) (fun x -> receiver c (step next x))
  = recv_x c

let history_p' (#p:prot) (t:partial_trace_of p) (s:partial_trace_of p) : prop =
  t `extended_to` s /\ True

let history_p (#p:prot) (t:partial_trace_of p) : MRef.stable_property extended_to =
  history_p' t

let history (#p:prot) (c:chan p) (t:partial_trace_of p) : slprop =
  pure (MRef.witnessed c.chan_chan.trace (history_p t))

let history_duplicable (#p:prot) (c:chan p) (t:partial_trace_of p)
  : SteelT unit (history c t) (fun _ -> history c t `star` history c t)
  = dup_pure _

let extension_until #p (previous:partial_trace_of p) (q:prot) =
  (t:partial_trace_of p{previous `extended_to` t /\ until t == q})

let recall_trace_ref #q (r:trace_ref q) (tr tr':partial_trace_of q)
  : SX.SteelXT (squash (history_p tr tr'))
           (MRef.pts_to r full_perm tr'  `star` pure (MRef.witnessed r (history_p tr)))
           (fun _ -> MRef.pts_to r full_perm tr')
  = as_steelx (fun _ -> MRef.recall #(partial_trace_of q) #full_perm #extended_to #(history_p tr) r tr');
    h_assert (MRef.pts_to r full_perm tr' `star` pure (history_p tr tr'));
    let s : squash (history_p tr tr') = frame_l (fun _ -> elim_pure #(history_p tr tr')) _ in
    h_commute _ _;
    h_elim_emp_l _;
    s

let witness_mref (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:MRef.ref a p)
            (fact:MRef.stable_property p)
            (v:Ghost.erased a)
            (u:squash (fact v))
  : SX.SteelXT unit (MRef.pts_to r q v)
                (fun _ -> MRef.pts_to r q v `star` pure (MRef.witnessed r fact))
  = as_steelx (fun _ -> MRef.witness #a #q #p r fact v u)

let witness_trace_ref #q (r:trace_ref q) (tr:partial_trace_of q)
  : SX.SteelXT unit (MRef.pts_to r full_perm tr)
                (fun _ -> MRef.pts_to r full_perm tr `star` pure (MRef.witnessed r (history_p tr)))
  = witness_mref #_ #full_perm #extended_to r (history_p tr) tr ()

let read_refine_mref (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#frame:a -> slprop)
                (r:MRef.ref a p)
  : SX.SteelXT a (h_exists (fun (v:a) -> MRef.pts_to r q v `star` frame v))
             (fun v -> MRef.pts_to r q v `star` frame v)
  = as_steelx (fun _ -> MRef.read_refine r)

let extend_history #q (c:chan q) (tr:partial_trace_of q) (v:chan_val)
  : SX.SteelXT (extension_of tr)
           (pts_to c.chan_chan.recv half v `star`
            history c tr `star`
            trace_until c.chan_chan.trace v)
           (fun tr' -> pts_to c.chan_chan.recv half v `star`
                    history c tr' `star`
                    trace_until c.chan_chan.trace v `star`
                    pure (until tr' == step v.chan_prot v.chan_msg))
  = let tr' = frame_l (fun _ -> read_refine_mref c.chan_chan.trace) _ in
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr) `star`
              (MRef.pts_to c.chan_chan.trace full_perm tr' `star`
               pure (until tr' == step v.chan_prot v.chan_msg)));
    reshuffle #_
              #(((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
                 (MRef.pts_to c.chan_chan.trace full_perm tr'  `star` history c tr)))
              ();
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (MRef.pts_to c.chan_chan.trace full_perm tr'  `star` history c tr));
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (MRef.pts_to c.chan_chan.trace full_perm tr'  `star` pure (MRef.witnessed c.chan_chan.trace (history_p tr))));
    let trref : trace_ref q = c.chan_chan.trace in
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (MRef.pts_to trref full_perm tr'  `star` pure (MRef.witnessed trref (history_p tr))));
    let tr_extension = frame_l (fun _ -> recall_trace_ref trref tr tr') _ in
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
               MRef.pts_to trref full_perm tr');
    frame_l (fun _ -> witness_trace_ref trref tr') _;
    h_assert ((pts_to c.chan_chan.recv half v `star` pure (until tr' == step v.chan_prot v.chan_msg)) `star`
              (MRef.pts_to trref full_perm tr' `star` history c tr'));
    reshuffle #_
              #((pts_to c.chan_chan.recv half v `star` history c tr') `star`
                (MRef.pts_to trref full_perm tr' `star` pure (until tr' == step v.chan_prot v.chan_msg)))
              ();
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              (MRef.pts_to trref full_perm tr' `star` pure (until tr' == step v.chan_prot v.chan_msg)));
    frame_l (fun _ -> frame_l (fun _ -> dup_pure _) _) _;
    frame_l (fun _ -> assoc_l _ _ _) _;
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              ((MRef.pts_to trref full_perm tr' `star` pure (until tr' == step v.chan_prot v.chan_msg))
                `star`
                pure (until tr' == step v.chan_prot v.chan_msg)));
    frame_l (fun _ -> frame (fun _ -> intro_trace_until trref tr' v) _) _;
    h_assert ((pts_to c.chan_chan.recv half v `star` history c tr') `star`
              (trace_until c.chan_chan.trace v `star` pure (until tr' == step v.chan_prot v.chan_msg)));
    reshuffle #_
              #(pts_to c.chan_chan.recv half v `star`
                history c tr' `star`
                trace_until c.chan_chan.trace v `star`
                pure (until tr' == step v.chan_prot v.chan_msg))
              ();
    return #(extension_of tr) #(fun tr' -> pts_to c.chan_chan.recv half v `star`
                                        history c tr' `star`
                                        trace_until c.chan_chan.trace v `star`
                                        pure (until tr' == step v.chan_prot v.chan_msg)) tr'

let extend_historyT #q (#[@@framing_implicit] tr:partial_trace_of q)
                       (#[@@framing_implicit] v:chan_val)
                       (c:chan q)
  : SteelT (extension_of tr)
           (pts_to c.chan_chan.recv half v `star`
            history c tr `star`
            trace_until c.chan_chan.trace v)
           (fun tr' -> pts_to c.chan_chan.recv half v `star`
                    history c tr' `star`
                    trace_until c.chan_chan.trace v `star`
                    pure (until tr' == step v.chan_prot v.chan_msg))
  = extend_history c tr v

let lift_steelXT (#a:_) (#b:(a -> Type)) (#p:a -> slprop) (#q:(x:a -> b x -> slprop))
                 (f: (x:a -> SX.SteelXT (b x) (p x) (q x)))
                 (x:a)
  : SteelT (b x) (p x) (q x)
  = f x

let intro_in_state_T (r:ref chan_val) (p:prot) (v:chan_val_p p)
  : SteelT unit (pts_to r half v) (fun _ -> in_state r p)
  = Steel.Effect.intro_pure (in_state_prop p v);
    Steel.Effect.intro_exists v (fun (v:chan_val) -> pts_to r half v `star` in_state_slprop p v)

let prot_equals #q  (#[@@framing_implicit]p:_) (#[@@framing_implicit] vr:chan_val) (cc:chan q)
  : Steel unit
          (pts_to cc.chan_chan.recv half vr `star` receiver cc p)
          (fun _ -> pts_to cc.chan_chan.recv half vr `star` receiver cc p)
          (requires fun _ -> True)
          (ensures fun _ _ _ -> step vr.chan_prot vr.chan_msg == p)
  = let vr' = Steel.Effect.Atomic.witness_h_exists () in
    Steel.Utils.higher_ref_pts_to_injective_eq cc.chan_chan.recv vr _;
    Steel.Effect.change_slprop (in_state_slprop _ _) (in_state_slprop p vr) (fun _ -> ());
    Steel.Utils.elim_pure _;
    intro_in_state_T _ _ vr

let witness_trace_until #q (#[@@framing_implicit] vr:chan_val) (r:trace_ref q)
  : SteelT (partial_trace_of q)
           (trace_until r vr)
           (fun tr -> trace_until r vr `star` pure (MRef.witnessed r (history_p tr)))
  = let tr = MRef.read_refine r in
    MRef.witness r (history_p tr) tr ();
    intro_trace_untilT r tr vr;
    tr

let intro_chan_inv_auxT #p  (#[@@framing_implicit] vs : chan_val)
                            (#[@@framing_implicit] vr : chan_val)
                            (c:chan_t p)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_cond vs vr)
                 (fun _ -> chan_inv c)
  = intro_chan_inv_aux c vs vr

let trace #q (cc:chan q)
  : SteelT (partial_trace_of q) emp (fun tr -> history cc tr)
  = let _ = send_receive_prelude cc in
    let tr = witness_trace_until cc.chan_chan.trace in
    intro_chan_inv_auxT cc.chan_chan;
    Steel.SpinLock.release cc.chan_lock;
    tr

let extend_trace (#q:prot) (#p:prot) (cc:chan q) (tr:partial_trace_of q)
  : SteelT (extension_of tr)
           (receiver cc p `star` history cc tr)
           (fun t -> receiver cc p `star` history cc t `star` pure (until t == p))
  = let _ = send_receive_prelude cc in
    let tr' = extend_historyT cc in
    let _ = prot_equals cc in
    Steel.Effect.change_slprop (pure (until tr' == _)) (pure (until tr' == p)) (fun _ -> ());
    intro_chan_inv_auxT cc.chan_chan;
    Steel.SpinLock.release cc.chan_lock;
    tr'
