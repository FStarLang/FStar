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

```pulse //tail_for_cons$
ghost
fn tail_for_cons (#t:Type) (v:node_ptr t) (#n:node t) (tl:erased (list t))
requires 
  pts_to v n
ensures 
  (is_list n.tail tl @==> is_list (Some v) (n.head::tl))
{
  ghost
  fn aux ()
  requires 
    pts_to v n ** is_list n.tail tl
  ensures 
    is_list (Some v) (n.head::tl)
  {
    intro_is_list_cons (Some v) v
  };
  I.intro _ _ _ aux;
}
```


```pulse //tail$
fn tail (#t:Type) (x:llist t)
requires is_list x 'l ** pure (Some? x)
returns y:llist t
ensures exists* tl.
    is_list y tl **
    (is_list y tl @==> is_list x 'l) **
    pure (Cons? 'l /\ tl == Cons?.tl 'l)
{ 
    let np = Some?.v x;
    is_list_case_some x np;
    with node tl. _;
    let nd = !np;
    rewrite each node.tail as nd.tail;
    tail_for_cons np tl;
    nd.tail
}
```

```pulse
fn op_Bang_Bang (#a:Type) (r:ref a)
requires pts_to r #p 'v
returns v:a
ensures pts_to r #p 'v ** pure (v == 'v)
{ !r }
```

```pulse //length_iter$
fn length_iter (#t:Type) (x: llist t)
requires is_list x 'l
returns n:nat
ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  open I;
  let mut cur = x;
  let mut ctr = 0; 
  I.refl (is_list x 'l); //initialize the trade for the invariant
  while (
    with _b _n _ll _sfx. _; // bind the existential variables in the invariant ...
    let v = !cur;           // !cur transformts pts_to x _ll into pts_to x v
    rewrite each _ll as v;  // rewrite the rest of the context to use v instead of _ll
    Some? v
  )
  invariant b.  
  exists* n ll suffix.
    pts_to ctr n **
    pts_to cur ll **
    is_list ll suffix **
    pure (n == List.Tot.length 'l - List.Tot.length suffix /\
          b == (Some? ll)) **
    (is_list ll suffix @==> is_list x 'l)
  {
    with _n _ll _suffix. _; //bind existential variables in the invariant
    let n = !ctr;
    let ll = !cur;
    rewrite each _ll as ll; //again, rewrite the context to use ll instead of _ll
    let next = tail ll;     //tail gives us back a trade
    with tl. _;
    I.trans (is_list next tl) _ _; //extend the trade, transittively
    cur := next;
    ctr := n + 1;
  };
  with _n ll _sfx. _;
  is_list_case_none ll; //this tells us that suffix=[]; so n == List.Tot.length 'l
  I.elim _ _;           //regain ownership of x, giving up ll
  let n = !ctr;
  n
}
```