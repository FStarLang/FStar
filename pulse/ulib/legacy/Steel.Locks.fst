module Steel.Locks
open Steel.Resource
module HS = FStar.HyperStack
let lock_addr = nat

noeq
type lock_entry : Type u#1 =
  | LockAvailable:
    r:resource ->
    h:HS.mem { inv_of r h } ->
    lock_entry

  | LockAcquired:
    r:resource ->
    lock_entry

let resource_of_lock_entry (l:lock_entry) : resource =
  match l with
  | LockAvailable r _
  | LockAcquired r -> r

let pre_lock_map = Map.t lock_addr (option lock_entry)

let lock_map (l:lock_addr) =
  m:pre_lock_map{
    (forall (x:lock_addr{x < l}). Some? (Map.sel m x)) /\ //locks once allocated, are never reclaimed
    (forall (x:lock_addr{x >= l}). Map.sel m x == None)   //addresses above lock_addr are free
  }

noeq
type lock_memory = {
  next_addr: lock_addr;
  store: lock_map next_addr
}

let lock_memory_preorder : Preorder.preorder lock_memory =
  fun m0 m1 ->
    m1.next_addr >= m0.next_addr /\ //locks remain allocated
    (forall (l:lock_addr{l < m0.next_addr}).
      let Some l0 = Map.sel m0.store l in
      let Some l1 = Map.sel m1.store l in
      resource_of_lock_entry l0 == //and always associated with the
      resource_of_lock_entry l1)   //same resource


(**
 * h0 `can_be_joined_into` h1  if
 *   - all the locations in h0 are beneath the allocation counters of h1
 *   - the locations in h0 are disjoint from the locations in h1
 * This relation is not symmetric
 *)
assume
val can_be_joined_into (h0 h1:HS.mem) : prop

assume
val join (h0:HS.mem) (h1:HS.mem {h0 `can_be_joined_into` h1})
  : Tot HS.mem

assume
val split (h:HS.mem) (r:resource{inv_of r h})
  : Tot (hr:HS.mem { inv_of r hr } &
          hr':HS.mem { hr `can_be_joined_into` hr' })

assume
val join_split (h:HS.mem) (r:resource)
  : Lemma
    (requires
      inv_of r h)
    (ensures
      (let (| hr, hs |) = split h r in
       join hr hs == h))

assume
val split_frames (h:HS.mem) (r0 r1:resource)
  : Lemma
    (requires
      inv_of (r0 <*> r1) h)
    (ensures
      (let (| h0, h1 |) = split h r0 in
       inv_of r0 h0 /\
       inv_of r1 h1))

assume
val join_frames (h0 h1:HS.mem) (r0 r1:resource)
  : Lemma
    (requires
      h0 `can_be_joined_into` h1 /\
      inv_of r0 h0 /\
      inv_of r1 h1)
    (ensures
      inv_of (r0 <*> r1) (join h0 h1))

let compatible (h:HS.mem) (m:lock_memory) =
  forall (l:lock_addr).
    match Map.sel m.store l with
    | Some (LockAvailable r h') ->
      h' `can_be_joined_into` h
    | _ -> True

noeq
type memory = {
  hs_mem: HS.mem;
  l_mem: lock_memory;
  compat: squash (compatible hs_mem l_mem)
}

let memory_evolves : Preorder.preorder memory =
  fun m0 m1 ->
    FStar.HyperStack.ST.mem_rel m0.hs_mem m1.hs_mem /\
    lock_memory_preorder m0.l_mem m1.l_mem

let mem_predicate = memory -> Type0
let stable (p:mem_predicate) = forall (m0 m1:memory). p m0 /\ m0 `memory_evolves` m1 ==> p m1
let witnessable = m:mem_predicate{stable m}

assume
val witnessed (p:witnessable) : Type0

assume
val lemma_functoriality (p:witnessable{witnessed p}) (q:witnessable{(forall m. p m ==> q m)})
  : Lemma (witnessed q)

let lock_addr_for_resource (a:lock_addr) (r:resource)
  : witnessable
  = fun (m:memory) ->
      match Map.sel m.l_mem.store a with
      | Some l -> resource_of_lock_entry l == r
      | _ -> False

let lock (r:resource) : Type u#0 = a:lock_addr {witnessed (lock_addr_for_resource a r)}

new_effect STATE = STATE_h memory

let pre           = st_pre_h memory
let post (a:Type) = st_post_h memory a
let wp (a:Type)   = st_wp_h memory a

unfold
let lift_hs_state_to_state
  (a:Type)
  (wp:FStar.HyperStack.ST.gst_wp a)
  (p:post a) (m:memory) =
    wp
      (fun a h ->
        h `compatible` m.l_mem /\ //Can we hide this with effect layering?
        p a ({m with hs_mem=h}))
    m.hs_mem


unfold
let lift_div_to_state
  (a:Type)
  (wp:pure_wp a)
  (p:post a) (m:memory) =
    wp (fun a -> p a m)

sub_effect DIV ~> STATE = lift_div_to_state
// //sub_effect FStar.HyperStack.ST.STATE ~> STATE = lift_hs_state_to_state
// sub_effect FStar.HyperStack.ST.STATE ~> STATE = lift_hs_state_to_state

assume
val get (_:unit) :
  STATE memory
    (fun k m -> k m m)

assume
val put (m:memory) :
  STATE unit
    (fun k m0 -> m0 `memory_evolves` m /\ k () m)

assume
val witness (p:witnessable) :
  STATE unit
    (fun k m -> p m /\ (witnessed p ==> k () m))

assume
val recall (p:witnessable) :
  STATE unit
    (fun k m -> witnessed p /\ (p m ==> k () m))


effect ST (a:Type) (p:pre) (q:memory -> post a) =
  STATE a (fun k m -> p m /\ (forall x m'. q m x m' ==> k x m'))

module RST = Steel.RST

effect RST
  (a: Type)
  (res0: resource)
  (res1: a -> resource)
  = ST
  a
  (fun (m0:memory) ->
    let h0 = m0.hs_mem in
    inv_of res0 h0 /\
    RST.rst_inv res0 h0)
  (fun m0 x m1 ->
    let h0 = m0.hs_mem in
    let h1 = m1.hs_mem in
    inv_of res0 h0 /\
    RST.rst_inv res0 h0 /\
    inv_of (res1 x) h1 /\
    RST.rst_inv (res1 x) h1 /\
    RST.modifies res0 (res1 x) h0 h1)

let new_lock (r:resource)
  : RST (lock r)
    (requires r)
    (ensures fun _ -> empty_resource)
  = let memory = get () in
    let (| hr, rest |) = split memory.hs_mem r in
    let lock_addr = memory.l_mem.next_addr in
    let store = Map.upd memory.l_mem.store lock_addr (Some (LockAvailable r hr)) in
    let l_mem' =  {
      next_addr = lock_addr + 1;
      store = store
    }
    in
    assume (rest `compatible` l_mem');
    assume (memory.hs_mem `FStar.HyperStack.ST.mem_rel` rest);
    let memory' = {memory with hs_mem = rest; l_mem = l_mem' } in
    put memory';
    assume (inv_of empty_resource rest);
    assume (RST.rst_inv empty_resource rest);
    assume (RST.modifies r empty_resource memory.hs_mem rest);
    witness (lock_addr_for_resource lock_addr r);
    lock_addr

let rec lock_acquire (#r:resource) (l:lock r)
  : RST unit
    (requires empty_resource)
    (ensures fun _ -> r)
  = recall (lock_addr_for_resource l r);
    let memory = get () in
    match Map.sel memory.l_mem.store l with
    | Some (LockAcquired _) ->
      lock_acquire l

    | Some (LockAvailable _ h) ->
      let h' = join h memory.hs_mem in
      join_frames h memory.hs_mem r empty_resource;
      assert (inv_of (r <*> empty_resource) h');
      let l_mem =
        { memory.l_mem
          with store = Map.upd memory.l_mem.store l (Some (LockAcquired r))
        }
      in
      assert (memory.l_mem `lock_memory_preorder` l_mem);
      assume (memory.hs_mem `FStar.HyperStack.ST.mem_rel` h');
      assert (memory.hs_mem `compatible` l_mem);
      assume (h' `compatible` l_mem);
      let memory' = {
        memory with
          hs_mem = h';
          l_mem = l_mem
      } in
      put memory';
      assert (inv_of r h');
      assume (RST.rst_inv r h');
      assume (RST.modifies empty_resource r memory.hs_mem h')

let lock_release (#r:resource) (l:lock r)
  : RST unit
    (requires r)
    (ensures fun _ -> empty_resource)
  = recall (lock_addr_for_resource l r);
    let memory = get () in
    match Map.sel memory.l_mem.store l with
    | Some (LockAcquired _) ->
      let (| hr, rest |) = split memory.hs_mem r in
      let store = Map.upd memory.l_mem.store l (Some (LockAvailable r hr)) in
      let l_mem' = {
        memory.l_mem with
        store = store
      }
      in
      assume (rest `compatible` l_mem');
      assume (memory.hs_mem `FStar.HyperStack.ST.mem_rel` rest);
      let memory' = {memory with hs_mem = rest; l_mem = l_mem' } in
      put memory';
      assume (inv_of empty_resource rest);
      assume (RST.rst_inv empty_resource rest);
      assume (RST.modifies r empty_resource memory.hs_mem rest)

    | Some (LockAvailable _ h) ->
      //exclude this case by showing a contradiction with compatibility
      assume (inv_of empty_resource memory.hs_mem);
      assume (RST.rst_inv empty_resource memory.hs_mem);
      assume (RST.modifies r empty_resource memory.hs_mem memory.hs_mem)
