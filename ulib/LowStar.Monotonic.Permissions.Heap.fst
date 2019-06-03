module LowStar.Monotonic.Permissions.Heap

module H = FStar.Monotonic.Heap
module F = FStar.FunctionalExtensionality

open FStar.Preorder

let permission = nat

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

val heap: Type u#1
noeq
type heap =
  { mheap : H.heap;
    perms : nat -> GTot value_perms } // For each memory address (given by addr_of), we have a map of permissions for this value

val ref (a:Type0) (rel:preorder a) : Type0
noeq
type ref a rel =
  { mref : H.mref a rel ;
    pid : pos}

val addr_of (#a:Type0) (#rel:preorder a) (r:ref a rel) : GTot nat
let addr_of #a #rel r = H.addr_of r.mref

val contains: #a:Type0 -> #rel:preorder a -> heap -> ref a rel -> Type0
let contains #a #rel h r =
  H.contains h.mheap r.mref /\                         // The ref is in the original heap
  (h.perms (H.addr_of r.mref)).perm_map (r.pid) > 0   // We have a non-empty permission: we can read

val writeable: #a:Type0 -> #rel:preorder a -> heap -> ref a rel -> Type0
let writeable #a #rel h r =
  let v_perms = h.perms (addr_of r) in
  H.contains h.mheap r.mref /\                             // The ref is in the original heap
  (v_perms).perm_map (r.pid) = v_perms.current_max       // We have the full permission: we can write

val sel_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:ref a rel{h `contains` r} -> Tot a
let sel_tot #a #rel h r = H.sel_tot h.mheap r.mref

val upd_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:ref a rel{h `writeable` r} -> x:a -> Tot heap
let upd_tot #a #rel h r x = 
  {h with mheap = H.upd_tot h.mheap r.mref x}

val alloc: #a:Type0 -> rel:preorder a -> heap -> a -> mm:bool -> Tot (ref a rel * heap)
let alloc #a rel h x mm =
  let new_r, mheap' = H.alloc rel h.mheap x mm in
  let perms' = (fun (n:nat) -> if n = H.addr_of new_r then new_value_perms () else h.perms n) in
  {mref = new_r; pid = 1}, {mheap = mheap'; perms = perms'}

val distinct: #a:Type0 -> #rel:preorder a -> ref a rel -> ref a rel -> GTot bool
let distinct #a #rel r1 r2 =
  addr_of r1 <> addr_of r2 || r1.pid <> r2.pid

// Share the permissions between the given ref and a newly created ref. Both are contained, but not 
// writeable anymore if the first one initially was
// Only GTot because of H.addr_of being GTot. Could be solved with friend
val share: #a:Type -> #rel:preorder a -> h:heap -> r:ref a rel{h `contains` r} -> GTot (heap * ref a rel * ref a rel)
let share #a #rel h r =
  let v_perms = h.perms (addr_of r) in
  let current_max' = v_perms.current_max + 1 in
  let perm_map' = F.on_dom pos (fun (x:pos) ->
    if x = current_max' then (1 <: permission) else v_perms.perm_map x) in
  let v_perms' = // :value_perms =
    { current_max = current_max'; perm_map = perm_map' } in
  admit()
  
