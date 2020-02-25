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

let chan_inv_cond (c:chan_t) (vsend:chan_val) (vrecv:chan_val) =
      (if vsend.chan_ctr = vrecv.chan_ctr
      then pure (vsend == vrecv)
      else pure (more vrecv.chan_prot /\ vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg))

let chan_inv_recv (c:chan_t) (vsend:chan_val) =
  h_exists (fun (vrecv:chan_val) ->
      pts_to c.recv half vrecv `star` chan_inv_cond c vsend vrecv)

let chan_inv (c:chan_t) : hprop =
  h_exists (fun (vsend:chan_val) ->
    pts_to c.send half vsend `star` chan_inv_recv c vsend)

noeq
type chan = {
  chan_chan : chan_t;
  chan_lock : lock (chan_inv chan_chan)
}

let in_state (r:ref chan_val) (p:prot) =
  h_exists (fun (vsend:chan_val) ->
    pure (more vsend.chan_prot /\ p == step vsend.chan_prot vsend.chan_msg) `star`
    pts_to r half vsend)

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

let send_pre (p:prot{more p}) (c:chan_t) (vs vr:chan_val) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   chan_inv_cond c vs vr `star`
   in_state c.send p)

let send_pre_split (p:prot{more p}) (c:chan_t) (vs vr:chan_val) (b:bool) : hprop =
  (pts_to c.send half vs `star`
   pts_to c.recv half vr `star`
   (if b then pure (vs == vr) else  pure (more vr.chan_prot /\ vs.chan_prot == step vr.chan_prot vr.chan_msg)) `star`
   in_state c.send p)


let send_pre_available (p:prot{more p}) (c:chan_t) (vs vr:chan_val) : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     pure (vs == vr) `star`
     in_state c.send p)

let send_pre_blocked (p:prot{more p}) (c:chan_t) (vs vr:chan_val) : hprop =
    (pts_to c.send half vs `star`
     pts_to c.recv half vr `star`
     pure (more vr.chan_prot /\ vs.chan_prot == step vr.chan_prot vr.chan_msg) `star`
     in_state c.send p)

let send_cond (#p:prot{more p}) (c:chan) (x:msg_t p) (vs vr:chan_val)
              (then_: (unit -> SteelT unit (send_pre_available p c.chan_chan vs vr) (fun _ -> sender c (step p x))))
              (else_: (unit -> SteelT unit (send_pre_blocked p c.chan_chan vs vr) (fun _ -> sender c (step p x))))
    : SteelT unit (send_pre p c.chan_chan vs vr) (fun _ -> sender c (step p x))
    = let cc = c.chan_chan in
      h_assert (send_pre p cc vs vr);
      h_assert (send_pre_split p cc vs vr (vs.chan_ctr = vr.chan_ctr));
      cond (vs.chan_ctr = vr.chan_ctr) (send_pre_split p cc vs vr) _ then_ else_

assume
val send_available(#p:prot{more p}) (c:chan) (x:msg_t p) (vs vr:chan_val) (_:unit)
  : SteelT unit (send_pre_available p c.chan_chan vs vr) (fun _ -> sender c (step p x))

assume
val send_blocked (#p:prot{more p}) (c:chan) (x:msg_t p) (vs vr:chan_val)
                 (loop:(unit ->SteelT unit (sender c p) (fun _ -> sender c (step p x))))
                 (_:unit)
  : SteelT unit (send_pre_blocked p c.chan_chan vs vr) (fun _ -> sender c (step p x))

let assoc_l (p q r:hprop)
  : SteelT unit (p `star` (q `star` r)) (fun _ -> (p `star` q) `star` r)
  = h_admit #unit _ _

let rec send (#p:prot{more p}) (cc:chan) (x:msg_t p)
  : SteelT unit (sender cc p) (fun _ -> sender cc (step p x))
  = let c : chan_t = cc.chan_chan in
    let l : lock (chan_inv c) = cc.chan_lock in
    h_assert (in_state c.send p);
    h_intro_emp_l _;
    let _ = frame (fun _ -> acquire l) _ in
    h_assert (chan_inv c `star` in_state c.send p);
    let vs = frame (fun _ -> read_refine (chan_inv_recv c) c.send) _ in
    h_assert ((pts_to c.send half vs `star` chan_inv_recv c vs) `star` in_state c.send p);
    frame (fun _ -> h_commute _ _) _;
    assoc_r _ _ _;
    h_assert (chan_inv_recv c vs `star` (pts_to c.send half vs `star` in_state c.send p));
    let vr = frame (fun _ -> read_refine (chan_inv_cond c vs) c.recv) _ in
    h_assert ((pts_to c.recv half vr `star` chan_inv_cond c vs vr) `star` (pts_to c.send half vs `star` in_state c.send p));
    rearrange _ _ _ _;
    frame (fun _ -> h_commute _ _) _;
    assoc_l _ _ _;
    h_assert (send_pre p c vs vr);
    rewrite_eq_squash c cc.chan_chan (fun x -> send_pre p x vs vr);
    h_assert (send_pre p cc.chan_chan vs vr);
    send_cond #p cc x vs vr (send_available #p cc x vs vr)
                            (send_blocked #p cc x vs vr (fun _ -> send cc x))

let rec send (#p:prot{more p}) (c:chan) (x:msg_t p)
 : Steel unit
   (expects sender c p)
   (provides fun _ -> sender c (step p x))
 = acquire c.inv;
   let _, _, n0 = !c.chan.send in
   let _, _, n1 = !c.chan.recv in
   if n0 == n1 //last send received
   then (c.chan.send := (p, x, n0 + 1);
         release c.inv)
   else (release c.inv; send c x) //spin
