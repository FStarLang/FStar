module PulseTutorial.LinkedList
open Pulse.Lib.Pervasives
module S = Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
open FStar.List.Tot

//llist$
noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)
//llist$

//is_list$
let rec is_list #t (x:llist t) (l:list t)
: Tot vprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl -> 
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl
//is_list$

//boilerplate$
```pulse
ghost
fn elim_is_list_nil (#t:Type0) (x:llist t)
requires is_list x l ** pure (l == [])
ensures pure (x == None)
{
   rewrite each l as Nil #t;
   unfold (is_list x [])
}
```

```pulse
ghost
fn intro_is_list_nil (#t:Type0) (x:llist t)
requires pure (x == None)
ensures is_list x []
{
    fold (is_list x []);
}
```

```pulse
ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (l:list t) (head:t) (tl:list t)
requires is_list x l ** pure (l == head::tl)
ensures (
  exists* (p:node_ptr t) (tail:llist t).
    pure (x == Some p) **
    pts_to p { head; tail } **
    is_list tail tl
)
{
  rewrite each l as (head::tl);
  rewrite_by
    (is_list x (head::tl))
    (exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl)
    vprop_equiv_norm
    ()
}
```
    

```pulse
ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t) (#node:node t) (#tl:list t)
requires
  pts_to v node **
  is_list node.tail tl **
  pure (x == Some v)
ensures
  is_list x (node.head::tl)
{
    rewrite (pts_to v node) as (pts_to v { head=node.head; tail=node.tail });
    rewrite_by
        (exists* (v:node_ptr t) (tail:llist t).
          pure (x == Some v) **
          pts_to v { head=node.head; tail } **
          is_list tail tl)
        (is_list x (node.head::tl))
        vprop_equiv_norm
        ()
}
```
//boilerplate$

//is_list_cases$
let is_list_cases #t (x:llist t) (l:list t)
: vprop 
= match x with
  | None -> pure (l == [])
  | Some v -> 
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl
//is_list_cases$

```pulse //cases_of_is_list$
ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  match l {
    Nil -> { 
      elim_is_list_nil x;
      fold (is_list_cases None l);
      rewrite each (None #(ref (node t))) as x;
    }
    Cons head tl -> { 
      elim_is_list_cons x l head tl;
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
      fold (is_list_cases (Some v) l);
      rewrite each (Some #(ref (node t)) v) as x;
    }
  }
}
```

```pulse //is_list_case_none$
ghost
fn is_list_case_none (#t:Type) (x:llist t) (#l:list t)
requires is_list x l ** pure (x == None)
ensures is_list x l ** pure (l == [])
{
  cases_of_is_list x l;
  rewrite each x as (None #(ref (node t)));
  unfold (is_list_cases None l);
  intro_is_list_nil x;
}
```


```pulse //is_list_case_some$
ghost
fn is_list_case_some (#t:Type) (x:llist t) (v:node_ptr t) (#l:list t) 
requires is_list x l ** pure (x == Some v)
ensures
  exists* (node:node t) (tl:list t).
    pts_to v node **
    is_list node.tail tl **
    pure (l == node.head::tl)
{
  cases_of_is_list x l;
  rewrite each x as (Some v);
  unfold (is_list_cases (Some v) l);
}
```


```pulse //length$
fn rec length (#t:Type0) (x:llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  match x {
    None -> {
      is_list_case_none x;
      0
    }
    Some vl -> {
      is_list_case_some x vl;
      with _node _tl. _;
      let node = !vl;
      rewrite each _node.tail as node.tail; 
      let n = length #t node.tail;
      intro_is_list_cons x vl;
      (1 + n)
    }
  }
}
```

```pulse
fn rec length_tail (#t:Type0) (x:llist t) (k:nat)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == k + List.Tot.length 'l)
{
  match x {
    None -> {
      is_list_case_none x;
      k
    }
    Some vl -> {
      is_list_case_some x vl;
      with tail tl. assert (is_list #t tail tl);
      let n = !vl;
      rewrite each tail as n.tail; 
      let n = length_tail #t n.tail (1 + k);
      intro_is_list_cons x vl;
      n
    }
  }
}
```

module I = Pulse.Lib.Stick.Util
open I

```pulse
ghost
fn list_cons_if_list_tail (#t:Type) 
                          (v:node_ptr t)
                          (tl:erased (list t))
requires 
  pts_to v n
ensures 
  (is_list n.tail tl @==> is_list (Some v) (n.head::tl))
{
  ghost
  fn yields_elim ()
  requires 
    pts_to v n ** is_list n.tail tl
  ensures 
    is_list (Some v) (n.head::tl)
  {
    intro_is_list_cons (Some v) v
  };
  I.intro _ _ _ yields_elim;
}
```


```pulse
fn move_next (#t:Type) (x:llist t)
    requires is_list x 'l ** pure (Some? x)
    returns y:llist t
    ensures exists* tl.
        is_list y tl **
        (is_list y tl @==> is_list x 'l) **
        pure (Cons? 'l /\ tl == Cons?.tl 'l)
{ 
    let np = Some?.v x;
    is_list_case_some x np;
    let node = !np;
    with tail tl. assert (is_list #t tail tl);
    rewrite each tail as node.tail;
    list_cons_if_list_tail np tl;
    node.tail
}
```

module GR = Pulse.Lib.GhostReference
open Pulse.Lib.Forall.Util
let can_update (x:GR.ref int) = 
  forall* v. pts_to x #half_perm v @==>
             pts_to x #half_perm (v + 1)

```pulse
fn length_iter (#t:Type) (x: llist t)
    requires is_list x 'l
    returns n:nat
    ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  open I;
  let mut cur = x;
  let mut ctr = 0; 
  I.refl (is_list x 'l);
  while (
    with _b _n ll _sfx. _; 
    let v = !cur; 
    rewrite (pts_to cur v) as (pts_to cur ll);
    Some? v
  )
  invariant b.  
  exists* n ll suffix.
    pts_to ctr n **
    pts_to cur ll **
    is_list ll suffix **
    (is_list ll suffix @==> is_list x 'l) **
    pure (n == List.Tot.length 'l - List.Tot.length suffix) **
    pure (b == (Some? ll))
  {
    with _n _ll suffix. _;
    let n = !ctr;
    let ll = !cur;
    rewrite each _ll as ll;
    let next = move_next ll;
    with tl. assert (is_list next tl);
    I.trans (is_list next tl) (is_list ll suffix) (is_list x 'l);
    cur := next;
    ctr := n + 1;
  };
  with _n ll _sfx. _;
  is_list_cases_none ll;
  I.elim _ _;
  let n = !ctr;
  n
}
```