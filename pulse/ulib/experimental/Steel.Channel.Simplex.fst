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
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.HigherReference
open Steel.FractionalPermission
module MRef = Steel.MonotonicHigherReference
module H = Steel.HigherReference

let sprot = p:prot { more p }

noeq
type chan_val = {
  chan_prot : sprot;
  chan_msg  : msg_t chan_prot;
  chan_ctr  : nat
}

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

let chan_inv_step (vrecv vsend:chan_val) : vprop =
  pure (chan_inv_step_p vrecv vsend)

let chan_inv_cond (vsend:chan_val) (vrecv:chan_val) : vprop =
    if vsend.chan_ctr = vrecv.chan_ctr
    then pure (vsend == vrecv)
    else chan_inv_step vrecv vsend

let trace_until_prop #p (r:trace_ref p) (vr:chan_val) (tr: partial_trace_of p) : vprop =
  MRef.pts_to r full_perm tr `star`
  pure (until tr == step vr.chan_prot vr.chan_msg)

let trace_until #p (r:trace_ref p) (vr:chan_val) =
  h_exists (trace_until_prop r vr)

let chan_inv_recv #p (c:chan_t p) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star`
      trace_until c.trace vrecv `star`
      chan_inv_cond vsend vrecv)

let chan_inv #p (c:chan_t p) : vprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

let intro_chan_inv_cond_eqT (vs vr:chan_val)
  : Steel unit emp
               (fun _ -> chan_inv_cond vs vr)
               (requires fun _ -> vs == vr)
               (ensures fun _ _ _ -> True)
  = intro_pure (vs == vs);
    rewrite_slprop (chan_inv_cond vs vs) (chan_inv_cond vs vr) (fun _ -> ())

let intro_chan_inv_cond_stepT (vs vr:chan_val)
  : SteelT unit (chan_inv_step vr vs)
                (fun _ -> chan_inv_cond vs vr)
  = Steel.Utils.extract_pure (chan_inv_step_p vr vs);
    rewrite_slprop (chan_inv_step vr vs) (chan_inv_cond vs vr) (fun _ -> ())

let intro_chan_inv_auxT #p  (#vs : chan_val)
                            (#vr : chan_val)
                            (c:chan_t p)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_cond vs vr)
                 (fun _ -> chan_inv c)
  = intro_exists _ (fun (vr:chan_val) -> pts_to c.recv half vr `star` trace_until c.trace vr `star` chan_inv_cond vs vr);
    intro_exists _ (fun (vs:chan_val) -> pts_to c.send half vs `star` chan_inv_recv c vs)

let intro_chan_inv_stepT #p (c:chan_t p) (vs vr:chan_val)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr `star`
                 chan_inv_step vr vs)
                 (fun _ -> chan_inv c)
  = intro_chan_inv_cond_stepT vs vr;
    intro_chan_inv_auxT c

let intro_chan_inv_eqT #p (c:chan_t p) (vs vr:chan_val)
  : Steel unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 trace_until c.trace vr)
                 (fun _ -> chan_inv c)
                 (requires fun _ -> vs == vr)
                 (ensures fun _ _ _ -> True)
  = intro_chan_inv_cond_eqT vs vr;
    intro_chan_inv_auxT c

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

[@@__reduce__]
let in_state_slprop (p:prot) (vsend:chan_val) : vprop = pure (in_state_prop p vsend)

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pts_to r half vsend `star` in_state_slprop p vsend)

let sender #q (c:chan q) (p:prot) = in_state c.chan_chan.send p
let receiver #q (c:chan q) (p:prot) = in_state c.chan_chan.recv p

let intro_chan_inv #p (c:chan_t p) (v:chan_val)
  : SteelT unit (pts_to c.send half v `star`
                 pts_to c.recv half v `star`
                 trace_until c.trace v)
                (fun _ -> chan_inv c)
  = intro_chan_inv_eqT c v v

let chan_val_p (p:prot) = (vs0:chan_val { in_state_prop p vs0 })
let intro_in_state (r:ref chan_val) (p:prot) (v:chan_val_p p)
  : SteelT unit (pts_to r half v) (fun _ -> in_state r p)
  = intro_pure (in_state_prop p v);
    intro_exists v (fun (v:chan_val) -> pts_to r half v `star` in_state_slprop p v)

let msg t p = Msg Send unit (fun _ -> p)
let init_chan_val (p:prot) = v:chan_val {v.chan_prot == msg unit p}

let initial_trace (p:prot) : (q:partial_trace_of p {until q == p})
  = { to = p; tr=Waiting p}

let intro_trace_until #q (r:trace_ref q) (tr:partial_trace_of q) (v:chan_val)
  : Steel unit (MRef.pts_to r full_perm tr)
               (fun _ -> trace_until r v)
               (requires fun _ -> until tr == step v.chan_prot v.chan_msg)
               (ensures fun _ _ _ -> True)
  = intro_pure (until tr == step v.chan_prot v.chan_msg);
    intro_exists tr
          (fun (tr:partial_trace_of q) ->
             MRef.pts_to r full_perm tr `star`
             pure (until tr == (step v.chan_prot v.chan_msg)));
    ()

let chan_t_sr (p:prot) (send recv:ref chan_val) = (c:chan_t p{c.send == send /\ c.recv == recv})

let intro_trace_until_init  #p (c:chan_t p) (v:init_chan_val p)
  : SteelT unit (MRef.pts_to c.trace full_perm (initial_trace p))
                (fun _ -> trace_until c.trace v)
  = intro_pure (until (initial_trace p) == step v.chan_prot v.chan_msg);
    //TODO: Not sure why I need this rewrite
    rewrite_slprop (MRef.pts_to c.trace full_perm (initial_trace p) `star`
                          pure (until (initial_trace p) == step v.chan_prot v.chan_msg))
                   (MRef.pts_to c.trace full_perm (initial_trace p) `star`
                          pure (until (initial_trace p) == step v.chan_prot v.chan_msg))
                   (fun _ -> ());
    intro_exists (initial_trace p) (trace_until_prop c.trace v)

let mk_chan (#p:prot) (send recv:ref chan_val) (v:init_chan_val p)
  : SteelT (chan_t_sr p send recv)
           (pts_to send half v `star` pts_to recv half v)
           (fun c -> chan_inv c)
  = let tr: trace_ref p = MRef.alloc (extended_to #p) (initial_trace p) in
    let c = Mkchan_t send recv tr in
    rewrite_slprop
      (MRef.pts_to tr full_perm (initial_trace p))
      (MRef.pts_to c.trace full_perm (initial_trace p)) (fun _ -> ());
    intro_trace_until_init c v;
    rewrite_slprop
      (pts_to send half v `star` pts_to recv half v)
      (pts_to c.send half v `star` pts_to c.recv half v)
      (fun _ -> ());
    intro_chan_inv #p c v;
    let c' : chan_t_sr p send recv = c in
    rewrite_slprop (chan_inv c) (chan_inv c') (fun _ -> ());
    return c'

let new_chan (p:prot) : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)
  = let q = msg unit p in
    let v : chan_val = { chan_prot = q; chan_msg = (); chan_ctr = 0 } in
    let vp : init_chan_val p = v in
    let send = H.alloc v in
    let recv = H.alloc v in
    H.share recv;
    H.share send;
    (* TODO: use smt_fallback *)
    rewrite_slprop (pts_to send (half_perm full_perm) v `star`
                   pts_to send (half_perm full_perm) v `star`
                   pts_to recv (half_perm full_perm) v `star`
                   pts_to recv (half_perm full_perm) v)
                  (pts_to send half vp `star`
                   pts_to send half vp `star`
                   pts_to recv half vp `star`
                   pts_to recv half vp)
                  (fun _ -> ());
    let c = mk_chan send recv vp in
    intro_in_state send p vp;
    intro_in_state recv p vp;
    let l  = Steel.SpinLock.new_lock (chan_inv c) in
    let ch = { chan_chan = c; chan_lock = l } in
    rewrite_slprop (in_state send p) (sender ch p) (fun _ -> ());
    rewrite_slprop (in_state recv p) (receiver ch p) (fun _ -> ());
    return ch

[@@__reduce__]
let send_recv_in_sync (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : vprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     pure (vs == vr) `star`
     in_state r p)

[@@__reduce__]
let sender_ahead (r:ref chan_val) (p:prot{more p}) #q (c:chan_t q) (vs vr:chan_val)  : vprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     trace_until c.trace vr `star`
     chan_inv_step vr vs `star`
     in_state r p)

let update_channel (#p:sprot) #q (c:chan_t q) (x:msg_t p) (vs:chan_val) (r:ref chan_val)
  : SteelT chan_val
           (pts_to r full_perm vs `star` in_state_slprop p vs)
           (fun vs' -> pts_to r full_perm vs' `star` (in_state_slprop (step p x) vs' `star` chan_inv_step vs vs'))
  = elim_pure (in_state_prop p vs);
    let vs' = next_chan_val x vs in
    H.write r vs';
    intro_pure (in_state_prop (step p x) vs');
    intro_pure (chan_inv_step_p vs vs');
    return vs'

[@@__reduce__]
let send_pre_available (p:sprot) #q (c:chan_t q) (vs vr:chan_val)  = send_recv_in_sync c.send p c vs vr

let gather_r (#p:sprot) (r:ref chan_val) (v:chan_val)
  : SteelT unit
    (pts_to r half v `star` in_state r p)
    (fun _ -> pts_to r full_perm v `star` in_state_slprop p v)
  = let v' = witness_exists () in
    H.higher_ref_pts_to_injective_eq #_ #_ #_ #_ #v #_ r;
    H.gather #_ #_ #half #half #v #v r;
    rewrite_slprop (pts_to r (sum_perm half half) v) (pts_to r full_perm v) (fun _ -> ());
    rewrite_slprop (in_state_slprop p v') (in_state_slprop p v) (fun _ -> ())

let send_available (#p:sprot) #q (cc:chan q) (x:msg_t p) (vs vr:chan_val) (_:unit)
  : SteelT unit (send_pre_available p #q cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = Steel.Utils.extract_pure (vs == vr);
    Steel.Utils.rewrite #_ #(send_recv_in_sync cc.chan_chan.send p cc.chan_chan vs) vr vs;
    elim_pure (vs == vs);
    gather_r cc.chan_chan.send vs;
    let next_vs = update_channel cc.chan_chan x vs cc.chan_chan.send in
    H.share cc.chan_chan.send;
    intro_exists next_vs (fun (next_vs:chan_val) -> pts_to cc.chan_chan.send half next_vs `star` in_state_slprop (step p x) next_vs);
    intro_chan_inv_stepT cc.chan_chan next_vs vs;
    Steel.SpinLock.release cc.chan_lock

let extensible (#p:prot) (x:partial_trace_of p) = P.more x.to
let next_msg_t (#p:prot) (x:partial_trace_of p) = P.next_msg_t x.to

let next_trace #p (vr:chan_val) (vs:chan_val)
                  (tr:partial_trace_of p)
                  (s:squash (until tr == step vr.chan_prot vr.chan_msg))
                  (_:squash (chan_inv_step_p vr vs))
   : (ts:partial_trace_of p { until ts == step vs.chan_prot vs.chan_msg })
   = let msg : next_msg_t tr = vs.chan_msg in
     assert (extensible tr);
     extend_partial_trace tr msg

let next_trace_st #p (vr:chan_val) (vs:chan_val) (tr:partial_trace_of p)
  : Steel (extension_of tr)
          (chan_inv_step vr vs)
          (fun _ -> emp)
          (requires fun _ -> until tr == step vr.chan_prot vr.chan_msg)
          (ensures fun _ ts _ -> until ts == step vs.chan_prot vs.chan_msg)
  = elim_pure (chan_inv_step_p vr vs);
    let ts : extension_of tr = next_trace vr vs tr () () in
    return ts

let update_trace #p (r:trace_ref p) (vr:chan_val) (vs:chan_val)
  : Steel unit
          (trace_until r vr)
          (fun _ -> trace_until r vs)
          (requires fun _ -> chan_inv_step_p vr vs)
          (ensures fun _ _ _ -> True)
  = intro_pure (chan_inv_step_p vr vs);
    let tr = MRef.read_refine r in
    elim_pure (until tr == step vr.chan_prot vr.chan_msg);
    let ts : extension_of tr = next_trace_st vr vs tr in
    MRef.write r ts;
    intro_pure (until ts == step vs.chan_prot vs.chan_msg);
    intro_exists ts
      (fun (ts:partial_trace_of p) ->
         MRef.pts_to r full_perm ts `star`
         pure (until ts == step vs.chan_prot vs.chan_msg))

let recv_availableT (#p:sprot) #q (cc:chan q) (vs vr:chan_val) (_:unit)
  : SteelT (msg_t p)
    (sender_ahead cc.chan_chan.recv p cc.chan_chan vs vr)
    (fun x -> receiver cc (step p x))
  = elim_pure (chan_inv_step_p vr vs);
    gather_r cc.chan_chan.recv vr;
    elim_pure (in_state_prop p vr);
    H.write cc.chan_chan.recv vs;
    H.share cc.chan_chan.recv;
    assert (vs.chan_prot == p);
    let vs_msg : msg_t p = vs.chan_msg in
    intro_pure (in_state_prop (step p vs_msg) vs);
    intro_exists vs (fun (vs:chan_val) -> pts_to cc.chan_chan.recv half vs `star` in_state_slprop (step p vs_msg) vs);
    update_trace cc.chan_chan.trace vr vs;
    intro_chan_inv cc.chan_chan vs;
    Steel.SpinLock.release cc.chan_lock;
    vs_msg

#push-options "--ide_id_info_off"
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
    let _ = witness_exists () in
    let vr = H.read cc.chan_chan.recv in
    rewrite_slprop (trace_until _ _ `star` chan_inv_cond _ _)
                               (trace_until cc.chan_chan.trace vr `star` chan_inv_cond vs vr)
                               (fun _ -> ());
    return (vs, vr)

let rec send (#p:prot) (c:chan p) (#next:prot{more next}) (x:msg_t next)
  : SteelT unit (sender c next) (fun _ -> sender c (step next x))
  = let v = send_receive_prelude c in //matching v as vs,vr fails
    if (fst v).chan_ctr = (snd v).chan_ctr
    then (
      rewrite_slprop (chan_inv_cond (fst v) (snd v))
                    (pure (fst v == snd v))
                    (fun _ -> ());
      send_available c x (fst v) (snd v) () //TODO: inlining send_availableT here fails
    )
    else (
      rewrite_slprop (chan_inv_cond (fst v) (snd v))
                                 (chan_inv_step (snd v) (fst v))
                                 (fun _ -> ());
      intro_chan_inv_stepT c.chan_chan (fst v) (snd v);
      Steel.SpinLock.release c.chan_lock;
      send c x
    )

let rec recv (#p:prot) (#next:prot{more next}) (c:chan p)
  : SteelT (msg_t next) (receiver c next) (fun x -> receiver c (step next x))
  = let v = send_receive_prelude c in
    if (fst v).chan_ctr = (snd v).chan_ctr
    then (
      rewrite_slprop (chan_inv_cond (fst v) (snd v))
                                 (pure (fst v == snd v))
                                 (fun _ -> ());
      elim_pure (fst v == snd v);
      intro_chan_inv_eqT c.chan_chan (fst v) (snd v);
      Steel.SpinLock.release c.chan_lock;
      recv c
    )
    else (
      rewrite_slprop (chan_inv_cond (fst v) (snd v))
                                 (chan_inv_step (snd v) (fst v))
                                 (fun _ -> ());
      recv_availableT c (fst v) (snd v) ()
    )


let history_p' (#p:prot) (t:partial_trace_of p) (s:partial_trace_of p) : prop =
  t `extended_to` s /\ True

let history_p (#p:prot) (t:partial_trace_of p) : MRef.stable_property extended_to =
  history_p' t

let history (#p:prot) (c:chan p) (t:partial_trace_of p) : prop =
  MRef.witnessed c.chan_chan.trace (history_p t)

let recall_trace_ref #q (r:trace_ref q) (tr tr':partial_trace_of q)
  : Steel unit
          (MRef.pts_to r full_perm tr')
          (fun _ -> MRef.pts_to r full_perm tr')
          (requires fun _ -> MRef.witnessed r (history_p tr))
          (ensures fun _ _ _ -> history_p tr tr')
  = MRef.recall (history_p tr) r tr'

let prot_equals #q  (#p:_) (#vr:chan_val) (cc:chan q)
  : Steel unit
          (pts_to cc.chan_chan.recv half vr `star` receiver cc p)
          (fun _ -> pts_to cc.chan_chan.recv half vr `star` receiver cc p)
          (requires fun _ -> True)
          (ensures fun _ _ _ -> step vr.chan_prot vr.chan_msg == p)
  = let vr' = witness_exists () in
    H.higher_ref_pts_to_injective_eq #_ #_ #_ #_ #vr #_ cc.chan_chan.recv;
    rewrite_slprop (in_state_slprop _ _) (in_state_slprop p vr) (fun _ -> ());
    elim_pure _;
    intro_in_state _ _ vr

let witness_trace_until #q (#vr:chan_val) (r:trace_ref q)
  : Steel (partial_trace_of q)
          (trace_until r vr)
          (fun tr -> trace_until r vr)
          (requires fun _ -> True)
          (ensures fun _ tr _ -> MRef.witnessed r (history_p tr))
  = let tr = MRef.read_refine r in
    MRef.witness r (history_p tr) tr ();
    elim_pure (until tr == step vr.chan_prot vr.chan_msg);
    intro_trace_until r tr vr;
    tr

let trace #q (cc:chan q)
  : Steel (partial_trace_of q) emp (fun _ -> emp)
          (requires fun _ -> True)
          (ensures fun _ tr _ -> history cc tr)
  = let _ = send_receive_prelude cc in
    let tr = witness_trace_until cc.chan_chan.trace in
    intro_chan_inv_auxT cc.chan_chan;
    Steel.SpinLock.release cc.chan_lock;
    tr

let extend_history #q (#tr:partial_trace_of q)
                       (#v:chan_val)
                       (c:chan q)
  : Steel (extension_of tr)
          (pts_to c.chan_chan.recv half v `star`
            trace_until c.chan_chan.trace v)
           (fun tr' -> pts_to c.chan_chan.recv half v `star`
                    trace_until c.chan_chan.trace v)
           (requires fun _ -> history c tr)
           (ensures fun _ tr' _ -> history c tr' /\ until tr' == step v.chan_prot v.chan_msg)
  = let tr' = MRef.read_refine c.chan_chan.trace in
    let _ = recall_trace_ref c.chan_chan.trace tr tr' in
    MRef.witness c.chan_chan.trace (history_p tr') tr' ();
    elim_pure (until tr' == step v.chan_prot v.chan_msg);
    intro_trace_until c.chan_chan.trace tr' v;
    let tr'' : extension_of tr = tr' in
    tr''

let extend_trace (#q:prot) (#p:prot) (cc:chan q) (tr:partial_trace_of q)
  : Steel (extension_of tr)
          (receiver cc p)
          (fun t -> receiver cc p)
          (requires fun _ -> history cc tr)
          (ensures fun _ t _ -> until t == p /\ history cc t)
  = let _ = send_receive_prelude cc in
    let tr' = extend_history cc in
    let _ = prot_equals cc in
    intro_chan_inv_auxT cc.chan_chan;
    Steel.SpinLock.release cc.chan_lock;
    tr'
