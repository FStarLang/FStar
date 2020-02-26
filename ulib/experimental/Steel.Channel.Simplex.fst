module Steel.Channel.Simplex
module P = Steel.Channel.Protocol.Lower
open Steel.SpinLock
open Steel.Effect
open Steel.Memory
open Steel.Reference
open Steel.SteelT.Basics

assume
val pure (p:prop) : hprop

noeq
type chan_val = {
  chan_prot : prot;
  chan_msg  : msg_t chan_prot;
  chan_ctr  : nat
}

noeq
type chan_t = {
  send: ref chan_val;
  recv: ref chan_val;
}

let half : perm = Steel.Permissions.(half_permission full)

let sprot = p:prot { more p }
let step (s:sprot) (x:msg_t s) = step s x

let chan_inv_step_p (vrecv vsend:chan_val) : prop =
  (more vrecv.chan_prot /\
   vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg /\
   vsend.chan_ctr == vrecv.chan_ctr + 1)

let chan_inv_step (vrecv vsend:chan_val) =
  pure (chan_inv_step_p vrecv vsend)

let chan_inv_cond (c:chan_t) (vsend:chan_val) (vrecv:chan_val) =
    if vsend.chan_ctr = vrecv.chan_ctr
    then pure (vsend == vrecv)
    else chan_inv_step vrecv vsend

let chan_inv_recv (c:chan_t) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star` chan_inv_cond c vsend vrecv)

let chan_inv (c:chan_t) : hprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

let intro_chan_inv_step (c:chan_t) (vs next_vs:chan_val)
  : SteelT unit (pts_to c.send half next_vs `star`
                 chan_inv_step vs next_vs `star`
                 pts_to c.recv half vs)
                 (fun _ -> chan_inv c)
  = h_admit _ _


let intro_chan_inv_eq (c:chan_t) (vs vr:chan_val)
  : SteelT unit (pts_to c.send half vs `star`
                 pts_to c.recv half vr `star`
                 pure (vs == vr))
                 (fun _ -> chan_inv c)
  = h_admit _ _

noeq
type chan = {
  chan_chan : chan_t;
  chan_lock : lock (chan_inv chan_chan)
}


let in_state_prop (p:prot) (vsend:chan_val) : prop =
  more vsend.chan_prot /\ p == step vsend.chan_prot vsend.chan_msg

irreducible
let next_chan_val (#p:sprot) (x:msg_t p) (vs0:chan_val { in_state_prop p vs0 })
  : Tot (vs:chan_val{in_state_prop (step p x) vs /\ vs.chan_ctr == vs0.chan_ctr + 1})
  = {
      chan_prot = (step vs0.chan_prot vs0.chan_msg);
      chan_msg = x;
      chan_ctr = vs0.chan_ctr + 1
    }

let in_state_hprop (p:prot) (vsend:chan_val) : hprop = pure (in_state_prop p vsend)

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pts_to r half vsend `star` in_state_hprop p vsend)

let sender (c:chan) (p:prot) = in_state c.chan_chan.send p
let receiver (c:chan) (p:prot) = in_state c.chan_chan.recv p
let rearrange (p q r s:hprop)
  : SteelT unit ((p `star` q) `star` (r `star` s))
                (fun _ -> (p `star` r) `star` (q `star` s))
  = h_admit #unit _ _

let intro_chan_inv (c:chan_t) (v:chan_val)
  : SteelT unit (pts_to c.send half v `star` pts_to c.recv half v)
                (fun _ -> chan_inv c)
  = h_admit #unit _ _

let assoc_r (p q r:hprop)
  : SteelT unit ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))
  = h_admit #unit _ _

let intro_in_state (r:ref chan_val) (v:chan_val{more v.chan_prot}) (p:prot{p == step v.chan_prot v.chan_msg})
  : SteelT unit (pts_to r half v) (fun _ -> in_state r p)
  = h_admit #unit _ _

assume
val elim_pure (#p:prop)
  : SteelT (squash p) (pure p) (fun _ -> emp)

let eq #a (x y : a) :prop = x == y

assume
val intro_pure (#p:prop) (s:squash p)
  : SteelT unit emp (fun _ -> pure p)

let rewrite_eq_squash #a (x:a) (y:a{x==y}) (p:a -> hprop)
  : SteelT unit (p x) (fun _ -> p y)
  = h_assert (p y)

let rewrite_eq #a (x:a) (y:a) (p:a -> hprop)
  : SteelT unit (pure (eq x y) `star` p x) (fun _ -> p y)
  = let _ = frame (fun _ -> elim_pure #(eq x y)) (p x) in
    h_assert (emp `star` p x);
    h_commute _ _;
    h_affine _ _;
    h_assert (p x);
    assert (x == y);
    rewrite_eq_squash x y p

assume
val h_assume (#p:hprop) (q:hprop)
  : SteelT unit p (fun _ -> q)

//#push-options "--query_stats --debug Steel.Channel.Simplex --debug_level SMTQuery"
// let alloc_pair (a:Type) (x:a) : SteelT unit emp (fun _ -> emp) =
//   let r0 = alloc x in
open Steel.Permissions
let new_chan (p:prot)
  : SteelT chan emp (fun c -> sender c p `star` receiver c p)
  = let q = msg unit p in
    let v : chan_val = { chan_prot = q; chan_msg = (); chan_ctr = 0 } in
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
    rearrange _ _ _ _;
    h_assert ((pts_to send half v `star` pts_to recv half v) `star`
              (pts_to send half v `star` pts_to recv half v));
    let c = { recv=recv; send=send } in
    let _ = frame (fun _ -> intro_chan_inv c v) (pts_to send half v `star` pts_to recv half v) in
    h_assert (chan_inv c `star` (pts_to send half v `star` pts_to recv half v));
    h_commute _ _;
    h_assert ((pts_to send half v `star` pts_to recv half v) `star` chan_inv c);
    assoc_r _ _ _ ; //(pts_to send half v) (pts_to recv half v) (chan_inv c);
    h_assert (pts_to send half v `star` (pts_to recv half v `star` chan_inv c));
    let v : (v:chan_val{more v.chan_prot}) = v in
    let p : (p:prot{p == step v.chan_prot v.chan_msg}) = p in
    let _ = frame (fun _ -> intro_in_state send v p) _ in //(pts_to recv half v `star` chan_inv c) in
    h_assert (in_state send p `star` (pts_to recv half v `star` chan_inv c));
    h_commute _ _;
    assoc_r _ _ _;
    let _ = frame (fun _ -> intro_in_state recv v p) _ in
    h_assert (in_state recv p `star` (chan_inv c `star` in_state send p));
    h_commute _ _;
    assoc_r _ _ _;
    h_assert (chan_inv c `star` (in_state send p `star` in_state recv p));
    let l : lock (chan_inv c) = frame (fun _ -> new_lock (chan_inv c)) _ in
    let ch = { chan_chan = c; chan_lock = l } in
    h_assert (emp `star` (in_state send p `star` in_state recv p));
    h_commute _ _;
    h_affine _ _;
    h_assert (in_state send p `star` in_state recv p);
    rewrite_eq_squash send ch.chan_chan.send (fun s -> in_state s p `star` in_state recv p);
    rewrite_eq_squash recv ch.chan_chan.recv (fun r -> in_state ch.chan_chan.send p `star` in_state r p);
    h_assert (sender ch p `star` receiver ch p);
    return #chan #(fun ch -> (sender ch p `star` receiver ch p)) ch

let send_pre (r:ref chan_val) (p:prot{more p}) (c:chan_t) (vs vr:chan_val) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   chan_inv_cond c vs vr `star`
   in_state r p)

let send_pre_split (r:ref chan_val)  (p:prot{more p}) (c:chan_t) (vs vr:chan_val) (b:bool) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   (if b then pure (vs == vr) else chan_inv_step vr vs) `star`
   in_state r p)

let send_recv_in_sync (r:ref chan_val) (p:prot{more p}) (c:chan_t) (vs vr:chan_val)  : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     pure (vs == vr) `star`
     in_state r p)

let sender_ahead (r:ref chan_val) (p:prot{more p}) (c:chan_t) (vs vr:chan_val)  : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     chan_inv_step vr vs `star`
     in_state r p)

let channel_cases (r:ref chan_val) (#p:prot{more p}) (c:chan) (x:msg_t p) (vs vr:chan_val)
                  (then_: (unit -> SteelT unit (send_recv_in_sync r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
                  (else_: (unit -> SteelT unit (sender_ahead r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))))
    : SteelT unit (send_pre r p c.chan_chan vs vr) (fun _ -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_

let assoc_l (p q r:hprop)
  : SteelT unit (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = h_admit #unit _ _

let ghost_read_refine (#a:Type) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT (Ghost.erased a) (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = let x = read_refine q r in
    return (Ghost.hide x)

// let id (x:int{0 < x \/ x <= 0}) = if x < 0 then x else x

// assume val p : int -> hprop
// noeq type box = | Mk : r:int -> box
// let test (x:box)
//   : SteelT unit (p x.r `star` emp) (fun _ -> emp)
//   = let r = x.r in
//     h_commute (p r) emp;
//     h_assert emp

let pts_to_injective #a #p #q (r:ref a) (v0 v1:Ghost.erased a) (rest:Ghost.erased a -> hprop)
  : SteelT unit (pts_to r p v0 `star` pts_to r q v1 `star` rest v1)
                (fun _ -> pts_to r p v0 `star` pts_to r q v0 `star` rest v0)
  = h_admit _ _

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

let update_channel (#p:sprot) (c:chan_t) (x:msg_t p) (vs:chan_val) (r:ref chan_val)
  : SteelT chan_val
           (pts_to r full vs `star` in_state_hprop p vs)
           (fun vs' -> pts_to r full vs' `star` (in_state_hprop (step p x) vs' `star` chan_inv_step vs vs'))
  = h_admit #chan_val _ _

assume
val rearrange5 (p q r s t:hprop)
  : SteelT unit ((p `star` q) `star` ((r `star` s) `star` t))
         (fun _ -> ((p `star` r) `star` ((q `star` s) `star` t)))

let send_pre_available (p:sprot) (c:chan_t)  = send_recv_in_sync c.send p c

let gather_r (#p:sprot) (r:ref chan_val) (v:chan_val)
  : SteelT unit
    (pts_to r half v `star` in_state r p)
    (fun _ -> pts_to r full v `star` in_state_hprop p v)
  = h_commute _ _;
    h_assert (in_state r p `star` pts_to r half v);
    let v' = frame (fun _ -> ghost_read_refine (in_state_hprop p) r) _ in
    h_assert ((pts_to r half v' `star` in_state_hprop p v') `star` pts_to r half v);
    h_commute _ _;
    assoc_l _ _ _;
    h_assert ((pts_to r half v `star` pts_to r half v') `star` in_state_hprop p v');
    pts_to_injective #_ #half #half r (Ghost.hide v) v' (fun (v':Ghost.erased chan_val) -> in_state_hprop p v');
    h_assert (pts_to r half v `star` pts_to r half v `star` in_state_hprop p v);
    frame (fun _ -> gather r) _

//#push-options "--query_stats"
let send_available(#p:sprot) (cc:chan) (x:msg_t p) (vs vr:chan_val) (_:unit)
  : SteelT unit (send_pre_available p cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = let c = cc.chan_chan in
    h_assert (((pts_to c.send half vs `star`
                pts_to c.recv half vr) `star`
                pure (vs == vr)) `star`
                in_state c.send p);
    assoc_r _ _ _;
    h_commute _ _;
    assoc_r _ _ _;
    let _ = frame (fun _ -> elim_pure #(eq vs vr)) _ in
    assert (vs == vr);
    h_assert (emp `star` ( in_state c.send p `star`
                           (pts_to c.send half vs `star`
                           pts_to c.recv half vr)));
    h_elim_emp_l _;
    assoc_l _ _ _;
    h_commute _ _;
    h_assert (pts_to c.recv half vr `star` (in_state c.send p `star` pts_to c.send half vs));
    rewrite_eq_squash vr vs (fun (v:chan_val) -> (pts_to c.recv half v `star` (in_state c.send p `star` pts_to c.send half vs)));
    h_assert (pts_to c.recv half vs `star` (in_state c.send p `star` pts_to c.send half vs));
    h_commute _ _;
    frame (fun _ -> h_commute _ _) _;
    frame (fun _ -> gather_r c.send vs) _;
    h_assert ((pts_to c.send full vs `star` in_state_hprop p vs) `star`
               pts_to c.recv half vs);
    let next_vs = frame (fun _ -> update_channel c x vs c.send) _ in
    h_assert ((pts_to c.send full next_vs `star` (in_state_hprop (step p x) next_vs `star` chan_inv_step vs next_vs)) `star`
               pts_to c.recv half vs);
    assoc_r _ _ _;
    h_assert (pts_to c.send full next_vs `star`
              ((in_state_hprop (step p x) next_vs `star` chan_inv_step vs next_vs) `star`
               pts_to c.recv half vs));
    frame (fun _ -> share #_ #next_vs c.send) _;
    h_assert ((pts_to c.send half next_vs `star` pts_to c.send half next_vs) `star`
               ((in_state_hprop (step p x) next_vs `star` chan_inv_step vs next_vs) `star`
                 pts_to c.recv half vs));
    rearrange5 _ _ _ _ _;
    h_assert ((pts_to c.send half next_vs `star` in_state_hprop (step p x) next_vs) `star`
               ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                 pts_to c.recv half vs));
    frame (fun _ -> intro_h_exists next_vs (fun (next_vs:chan_val) -> pts_to c.send half next_vs `star` in_state_hprop (step p x) next_vs)) _;
    h_assert (sender cc (step p x) `star`
               ((pts_to c.send half next_vs `star` chan_inv_step vs next_vs) `star`
                 pts_to c.recv half vs));
    h_commute _ _;
    frame (fun _ -> intro_chan_inv_step c vs next_vs) _;
    h_assert (chan_inv c `star` sender cc (step p x));
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _

let rearrange_pqrs_qs_pr (p q r s:hprop)
  : SteelT unit
    (p `star` q `star` r `star` s)
    (fun _ -> (q `star` s) `star` (p `star` r))
  = h_admit _ _

assume
val intro_pure_p (#p:prop) (s:squash p) (h:hprop)
  : SteelT unit h (fun _ -> pure p `star` h)

let recv_available (#p:sprot) (cc:chan) (vs vr:chan_val) (_:unit)
  : SteelT (msg_t p)
    (sender_ahead cc.chan_chan.recv p cc.chan_chan vs vr)
    (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    h_assert (pts_to c.send half vs `star`
              pts_to c.recv half vr `star`
              chan_inv_step vr vs `star`
              in_state c.recv p);
    rearrange_pqrs_qs_pr _ _ _ _;
    frame (fun _ -> gather_r c.recv vr) _;
    h_assert ((pts_to c.recv full vr `star` in_state_hprop p vr) `star` (pts_to c.send half vs `star` chan_inv_step vr vs));
    h_commute _ _;
    frame (fun _ -> h_commute _ _) _;
    assoc_r _ _ _;
    h_assert (chan_inv_step vr vs `star` _);
    frame (fun _ -> elim_pure #(chan_inv_step_p vr vs)) _;
    h_elim_emp_l _;
    h_assert (pts_to c.send half vs `star`  (pts_to c.recv full vr `star` in_state_hprop p vr));
    assert (chan_inv_step_p vr vs);
    assert (vs.chan_prot == step vr.chan_prot vr.chan_msg);
    h_commute _ _;
    frame (fun _ -> h_commute _ _) _;
    assoc_r _ _ _;
    frame (fun _ -> elim_pure #(in_state_prop p vr)) _;
    h_elim_emp_l _;
    assert (vs.chan_prot == p);
    let s : squash (in_state_prop (step p vs.chan_msg) vs) = () in
    h_assert (pts_to c.recv full vr `star` pts_to c.send half vs);
    intro_pure_p s (pts_to c.recv full vr `star` pts_to c.send half vs);
    h_assert (in_state_hprop (step p vs.chan_msg) vs `star` (pts_to c.recv full vr `star` pts_to c.send half vs));
    h_commute _ _;
    assoc_r _ _ _;
    frame (fun _ -> write c.recv vs) _;
    h_assert (pts_to c.recv full vs `star` (pts_to c.send half vs `star` in_state_hprop (step p vs.chan_msg) vs));
    frame (fun _ -> share c.recv) _;
    h_assert ((pts_to c.recv half vs `star` pts_to c.recv half vs) `star`
              (pts_to c.send half vs `star` in_state_hprop (step p vs.chan_msg) vs));
    rearrange _ _ _ _;
    h_assert ((pts_to c.recv half vs `star` pts_to c.send half vs) `star`
              (pts_to c.recv half vs `star` in_state_hprop (step p vs.chan_msg) vs));
    h_commute _ _;
    let q = step p vs.chan_msg in
    h_assert ((pts_to c.recv half vs `star` in_state_hprop q vs) `star` (pts_to c.recv half vs `star` pts_to c.send half vs));
    frame (fun _ -> intro_h_exists vs (fun (vs:chan_val) -> (pts_to c.recv half vs `star` in_state_hprop q vs))) _;
    h_assert (receiver cc q `star` (pts_to c.recv half vs `star` pts_to c.send half vs));
    h_commute _ _;
    frame (fun _ -> h_commute _ _) _;
    frame (fun _ -> intro_chan_inv c vs) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    return #_ #(fun x -> receiver cc (step p x)) vs.chan_msg

let rearrange_pqr_prq (p q r:hprop)
  : SteelT unit (p `star` q `star` r)
                (fun _ -> p `star` r `star` q)
  = h_admit _ _

let send_pre_blocked (p:sprot) (c:chan_t)  = sender_ahead c.send p c

let send_blocked (#p:prot{more p}) (cc:chan) (x:msg_t p) (vs vr:chan_val)
                 (loop:(unit ->SteelT unit (sender cc p) (fun _ -> sender cc (step p x))))
                 (_:unit)
  : SteelT unit (send_pre_blocked p cc.chan_chan vs vr) (fun _ -> sender cc (step p x))
  = let c = cc.chan_chan in
    h_assert ((pts_to c.send half vs `star`
               pts_to c.recv half vr `star`
               chan_inv_step vr vs) `star`
               sender cc p);
    frame (fun _ -> rearrange_pqr_prq _ _ _) _;
    frame (fun _ -> intro_chan_inv_step c vr vs) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    loop ()

let send_receive_prelude (cc:chan)
  : SteelT (chan_val & chan_val)
           emp
           (fun v ->
             pts_to cc.chan_chan.send half (fst v) `star`
             pts_to cc.chan_chan.recv half (snd v) `star`
             chan_inv_cond cc.chan_chan (fst v) (snd v))
  = let c : chan_t = cc.chan_chan in
    let l : lock (chan_inv c) = cc.chan_lock in
    let _ = acquire l in
    h_assert (chan_inv c);
    let vs = read_refine (chan_inv_recv c) c.send in
    h_assert (pts_to c.send half vs `star` chan_inv_recv c vs);
    h_commute _ _;
    let vr = frame (fun _ -> read_refine (chan_inv_cond c vs) c.recv) _ in
    h_assert ((pts_to c.recv half vr `star` chan_inv_cond c vs vr) `star` pts_to c.send half vs);
    h_commute _ _;
    assoc_l _ _ _;
    let result : chan_val & chan_val = vs, vr in
    return #(chan_val & chan_val)
           #(fun result ->
              pts_to c.send half (fst result) `star`
              pts_to c.recv half (snd result) `star`
              chan_inv_cond c (fst result) (snd result))
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
let rec send (#p:prot{more p}) (cc:chan) (x:msg_t p)
  : SteelT unit (sender cc p) (fun _ -> sender cc (step p x))
  = h_intro_emp_l _;
    let vs_vr = frame (fun _ -> send_receive_prelude cc) _ in
    let vs = fst vs_vr in
    let vr = snd vs_vr in
    h_assert (send_pre cc.chan_chan.send p cc.chan_chan vs vr);
    channel_cases cc.chan_chan.send #p cc x vs vr (send_available #p cc x vs vr)
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
                  (r:ref chan_val) (#p:prot{more p}) (c:chan) (vs vr:chan_val)
                  (then_: (unit -> SteelT (msg_t p) (send_recv_in_sync r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
                  (else_: (unit -> SteelT (msg_t p) (sender_ahead r p c.chan_chan vs vr) (fun x -> in_state r (step p x))))
    : SteelT (msg_t p) (send_pre r p c.chan_chan vs vr) (fun x -> in_state r (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre r p cc vs vr);
      h_assert (send_pre_split r p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split r p cc vs vr) _ then_ else_


let intro_chan_inv_eq2 (c:chan_t) (vs vr:chan_val)
  : SteelT unit ((pts_to c.send half vs `star`
                  pts_to c.recv half vr) `star`
                  pure (vs == vr))
                 (fun _ -> chan_inv c)
  = h_admit _ _

let recv_blocked (#p:prot{more p}) (cc:chan) (vs vr:chan_val)
                 (loop:unit -> SteelT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x)))
                 (_:unit)
  : SteelT (msg_t p) (send_recv_in_sync cc.chan_chan.recv p cc.chan_chan vs vr) (fun x -> receiver cc (step p x))
  = let c = cc.chan_chan in
    frame (fun _ -> intro_chan_inv_eq2 c vs vr) _;
    frame (fun _ -> release cc.chan_lock) _;
    h_elim_emp_l _;
    loop ()

let rec recv (#p:prot{more p}) (cc:chan)
  : SteelT (msg_t p) (receiver cc p) (fun x -> receiver cc (step p x))
  = h_intro_emp_l _;
    let vs_vr = frame (fun _ -> send_receive_prelude cc) _ in
    let vs = fst vs_vr in
    let vr = snd vs_vr in
    h_assert (send_pre cc.chan_chan.recv p cc.chan_chan vs vr);
    channel_cases_recv cc.chan_chan.recv #p cc vs vr (recv_blocked #p cc vs vr (fun _ -> recv cc))
                                                     (recv_available #p cc vs vr)
