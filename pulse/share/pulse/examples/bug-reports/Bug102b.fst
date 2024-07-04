module Bug102b

open Pulse.Lib.Pervasives

noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)

let rec is_list #t (x:llist t) (l:list t)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (x == None)
    | head::tl -> 
      exists* (v:node_ptr t) (tail:llist t).
        pure (x == Some v) **
        pts_to v { head; tail } **
        is_list tail tl

```pulse
ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (head:t) (tl:list t)
  requires is_list x (head::tl)
  ensures (
    exists* (v:node_ptr t) (tail:llist t).
      pure (x == Some v) **
      pts_to v { head; tail } **
      is_list tail tl
  )
{
  unfold (is_list x (head::tl));
}
```

```pulse
ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (head:t) (tl:list t)
  requires (
    exists* (v:node_ptr t) (tail:llist t).
      pure (x == Some v) **
      pts_to v { head; tail } **
      is_list tail tl)
  ensures is_list x (head::tl)
{
  fold (is_list x (head::tl));
}
```
