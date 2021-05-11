module Steel.SelLockCoupling
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.SelSpinLock
open Steel.SelReference
open Steel.FractionalPermission

#push-options "--__no_positivity"
noeq
type llist (a:Type0) : Type0 = {
  v : a;
  next : ref (llist a);
  lock : lock_t
}
#pop-options


let rec llist_inv (#a:Type) (repr:list (a -> vprop)) (n:ref (llist a))
  = match repr with
    | [] -> emp
    | p::tl ->
      h_exists (fun (cell:llist a) ->
         p cell.v `star`
         pts_to n full_perm cell `star`
         pure (cell.lock `protects` llist_inv tl cell.next))
