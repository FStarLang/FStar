module Bug95

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util
open FStar.List.Tot

noeq
type node (t:Type0) = {
    value : t;
    dllprev : option (node_ptr t);
    dllnext : option (node_ptr t);
}

and node_ptr (t:Type0) = ref (node t)

let rec is_list_suffix
  #t (x:node_ptr t) (l:list t {Cons? l}) (prev:option (node_ptr t)) (tail:node_ptr t)
  : Tot vprop (decreases l)
  = match l with
    | [] -> emp
    | [n] ->
      exists* (v:node t).
        pts_to x v **
        pure (v.value == n /\
          v.dllnext == None /\
          v.dllprev == prev /\
          x == tail)
    | n::ns ->
      exists* (v:node t) (np:node_ptr t).
        pts_to x v **
        is_list_suffix np ns (Some x) tail **
        pure (v.value == n /\
          v.dllprev == prev /\
          v.dllnext == (Some np))

(* This fold used to fail. *)
```pulse
ghost
fn intro_is_list_singleton
  (#t:Type)
  (x : node_ptr t) (n : t)
  requires
      exists* (v:node t).
        pts_to x v **
        pure (v.value == n /\
          v.dllnext == None /\
          v.dllprev == None)
  ensures
    is_list_suffix x [n] None x
{
  fold (is_list_suffix x [n] None x);
}
```
