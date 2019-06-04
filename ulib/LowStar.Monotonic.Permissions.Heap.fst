module LowStar.Monotonic.Permissions.Heap

module H = FStar.Monotonic.Heap
module F = FStar.FunctionalExtensionality

open FStar.Preorder

private noeq
type perms_rec = {
  current_max : pos;
  perm_map    : F.restricted_t pos (fun (x:pos) -> permission)
}

let rec sum_until (f:pos -> permission) (n:nat) : GTot nat =
  if n = 0 then 0
  else f n + sum_until f (n - 1)

let value_perms = p:perms_rec{
  (forall (n:nat). n > p.current_max ==> p.perm_map n = 0) /\        // Permissions are null above currently split objects
  (sum_until p.perm_map p.current_max = p.current_max)} // The sum of permissions is the number of splits up till now

let new_value_perms () : value_perms =
   let f:F.restricted_t pos (fun (x:pos) -> permission) = 
     F.on_dom pos (fun (x:pos) -> if x = 1 then (1 <: permission) else (0 <: permission)) in
   { current_max = 1; perm_map = f }

noeq
type heap =
  { mheap : H.heap;
    perms : nat -> GTot value_perms } // For each memory address (given by addr_of), we have a map of permissions for this value

let emp =
  { mheap = H.emp;
    perms = fun n -> new_value_perms() }
    
noeq
type ref a rel =
  { mref : H.mref a rel ;
    pid : pos}

let addr_of #a #rel r = H.addr_of r.mref

let contains #a #rel h r =
  H.contains h.mheap r.mref /\                         // The ref is in the original heap
  (h.perms (H.addr_of r.mref)).perm_map (r.pid) > 0   // We have a non-empty permission: we can read

let writeable #a #rel h r =
  let v_perms = h.perms (addr_of r) in
  H.contains h.mheap r.mref /\                             // The ref is in the original heap
  (v_perms).perm_map (r.pid) = v_perms.current_max       // We have the full permission: we can write

let sel_tot #a #rel h r = H.sel_tot h.mheap r.mref

let upd_tot #a #rel h r x = 
  {h with mheap = H.upd_tot h.mheap r.mref x}

let alloc #a rel h x mm =
  let new_r, mheap' = H.alloc rel h.mheap x mm in
  let perms' = (fun (n:nat) -> if n = H.addr_of new_r then new_value_perms () else h.perms n) in
  {mref = new_r; pid = 1}, {mheap = mheap'; perms = perms'}

let distinct #a #rel r1 r2 =
  addr_of r1 <> addr_of r2 || r1.pid <> r2.pid

let rec same_prefix_same_sum_until (p1 p2:pos -> permission) (n:nat) : Lemma
  (requires forall (x:pos). x <= n ==> p1 x = p2 x)
  (ensures sum_until p1 n == sum_until p2 n)
  = if n = 0 then () else same_prefix_same_sum_until p1 p2 (n-1)

let share #a #rel h r =
  let v_perms = h.perms (addr_of r) in
  let current_max' = v_perms.current_max + 1 in
  let perm_map' = F.on_dom pos (fun (x:pos) ->
    if x = current_max' then (1 <: permission) else v_perms.perm_map x) in
  same_prefix_same_sum_until v_perms.perm_map perm_map' (current_max' - 1);
  let v_perms' :value_perms =
    { current_max = current_max'; perm_map = perm_map' } in
  let heap' = {mheap = h.mheap; perms = fun n -> if n = addr_of r then v_perms' else h.perms n} in
  heap', r, {r with pid = current_max'}

let rec sum_until_change (p1 p2:pos -> permission) (n:nat) (i:pos) (v:permission) : Lemma
  (requires (forall (x:pos). (x <= n /\ x <> i) ==> p1 x = p2 x) /\
            i <= n /\
            p2 i = v)
  (ensures sum_until p2 n = sum_until p1 n + v - p1 i)
  = if n = i then same_prefix_same_sum_until p1 p2 (n-1)
    else sum_until_change p1 p2 (n-1) i v

let merge #a #rel h r1 r2 =
  let v_perms = h.perms (addr_of r1) in
  let perm_map1' = F.on_dom pos (fun (x:pos) ->
    if x = r1.pid then (v_perms.perm_map r1.pid + v_perms.perm_map r2.pid <: permission)
    else v_perms.perm_map x) in
  let perm_map2' = F.on_dom pos (fun (x:pos) -> if x = r2.pid then (0 <: permission) else perm_map1' x) in
  sum_until_change v_perms.perm_map perm_map1' v_perms.current_max r1.pid (v_perms.perm_map r1.pid + v_perms.perm_map r2.pid);
  sum_until_change perm_map1' perm_map2' v_perms.current_max r2.pid 0;
  let v_perms' :value_perms =
    { current_max = v_perms.current_max; perm_map = perm_map2' } in
  let heap' = {mheap = h.mheap; perms = fun n -> if n = addr_of r1 then v_perms' else h.perms n} in
  heap', r1
