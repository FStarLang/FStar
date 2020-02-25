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

let chan_inv (c:chan_t) : hprop =
  h_exists (fun (vsend:chan_val) ->
  h_exists (fun (vrecv:chan_val) ->
    pts_to c.send half vsend `star`
    pts_to c.recv half vrecv `star`
    (if vsend.chan_ctr = vrecv.chan_ctr
     then pure (vsend == vrecv)
     else pure (more vrecv.chan_prot /\ vsend.chan_prot == step vrecv.chan_prot vrecv.chan_msg))))

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
