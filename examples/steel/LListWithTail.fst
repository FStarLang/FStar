module LListWithTail
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference
module LL = LList
module L = FStar.List.Tot.Base

noeq
type t (a: Type0) = {
  list: LL.t a;
  tail: ref (LL.cell a);
}

let llist_with_tail (#a: Type0) (x: t a) (l: list (LL.cell a)) : Tot slprop =
  LL.llist x.list l `star`
  pure (is_null x.tail == Nil? l) `star`
  begin match l with
  | [] -> emp
  | _ -> pts_to x.tail full_perm (L.last l)
  end

let empty (a: Type0) : Tot (t a) =
  {
    list = LL.null_llist;
    tail = null;
  }

