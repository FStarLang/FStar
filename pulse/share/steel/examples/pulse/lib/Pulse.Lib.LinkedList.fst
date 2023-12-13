module Pulse.Lib.LinkedList
open Pulse.Lib.Pervasives
module T = FStar.Tactics

noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and llist (t:Type0) = option (node_ptr t)

let mk_node #t (hd:t) (tl:llist t) : Tot (node t)
  = {head=hd; tail=tl}

let rec is_list #t (x:llist t) (l:list t)
  : Tot vprop (decreases l)
  = match l with
    | [] -> pure (x == None)
    | head::tl -> 
      exists* (v:node_ptr t) (tail:llist t).
        pure (x == Some v) **
        pts_to v (mk_node head tail) **
        is_list tail tl
    


let is_list_cases #t (x:llist t) (l:list t)
  : Tot vprop 
  = match x with
    | None -> pure (l == [])
    | Some v -> 
      exists* (n:node t) (tl:list t).
        pts_to v n **
        pure (l == n.head::tl) **
        is_list n.tail tl


```pulse
ghost
fn elim_is_list_nil (#t:Type0) (x:llist t) 
  requires is_list x []
  ensures pure(x == None)
{
   unfold (is_list x [])
}
```

```pulse
ghost
fn intro_is_list_nil (#t:Type0) (x:(x:llist t { x == None }))
    requires emp
    ensures is_list x []
{
    fold (is_list x [])
}
```

module T = FStar.Tactics

let prop_squash_idem (p:prop)
  : Tot (p == squash p)
  = admit()
//   FStar.PropositionalExtensionality.apply p (squash p)


#push-options "--no_tactics"
let rewrite_by (p:vprop) (q:vprop) 
               (t:unit -> T.Tac unit)
               (_:unit { T.with_tactic t (vprop_equiv p q) })
  : stt_ghost unit emp_inames p (fun _ -> q)
  = let pf : squash (vprop_equiv p q) = T.by_tactic_seman t (vprop_equiv p q) in
    prop_squash_idem (vprop_equiv p q);
    rewrite p q (coerce_eq () pf)
#pop-options


let norm_tac (_:unit) : T.Tac unit =
    T.mapply (`vprop_equiv_refl)
    
```pulse
ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (head:t) (tl:list t)
  requires is_list x (head::tl)
  ensures exists* (v:node_ptr t) (tail:llist t).
            pure (x == Some v) **
            pts_to v (mk_node head tail) **
            is_list tail tl
{

    rewrite_by (is_list x (head::tl))
               (exists* (v:node_ptr t)
                        (tail:llist t).
                    pure (x == Some v) **
                    pts_to v (mk_node head tail) **
                    is_list tail tl)
                norm_tac
                ()
}
```

```pulse
ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t) (#node:node t) (#tl:list t)
    requires pts_to v node ** is_list node.tail tl ** pure (x == Some v)
    ensures is_list x (node.head::tl)
{
    rewrite (pts_to v node) as (pts_to v (mk_node node.head node.tail));
    rewrite_by
         (exists* (v:node_ptr t) (tail:llist t).
                pure (x == Some v) **
                pts_to v (mk_node node.head tail) **
                is_list tail tl)
        (is_list x (node.head::tl))
        norm_tac
        ()
}
```
let elim_false (p:vprop) : stt_ghost unit emp_inames (pure False) (fun _ -> p) = Pulse.Lib.Core.elim_false unit (fun _ -> p)
let drop (p:vprop) : stt_ghost unit emp_inames p (fun _ -> emp) = admit()

// #push-options "--ext 'pulse:env_on_err'"
```pulse
ghost
fn cases_of_is_list (#t:Type) (x:llist t) (l:list t)
    requires is_list x l
    ensures is_list_cases x l
{
    match l {
        Nil -> { 
            rewrite (is_list x l) as (is_list x []);
            elim_is_list_nil x;
            rewrite (pure (l == [])) as (is_list_cases x l);
        }
        Cons head tl -> { 
            rewrite (is_list x l) as (is_list x (head::tl));
            elim_is_list_cons x head tl;
            assert pure (Some? x);
            match x {
                None -> {  
                    elim_false (is_list_cases x l);
                    with tail. assert(is_list tail tl);
                    drop (is_list tail tl);
                    with v. assert (pts_to v (mk_node head tail));
                    drop (pts_to v (mk_node head tail));
                }
                Some v -> { 
                    with tail. assert (is_list #t tail tl);
                    with w. assert (pts_to w (mk_node head tail));
                    rewrite (pts_to w (mk_node head tail)) as
                            (pts_to v (mk_node head tail));
                    rewrite (is_list tail tl) as 
                            (is_list (mk_node head tail).tail tl);
                    fold (is_list_cases (Some v) l);
                    rewrite (is_list_cases (Some v) l) as
                            (is_list_cases x l)
                }
            }
        }
    }
}
```

```pulse
ghost
fn is_list_of_cases (#t:Type) (x:llist t) (l:list t)
    requires is_list_cases x l
    ensures is_list x l
{
    match x {
        None -> { 
            rewrite (is_list_cases x l) as pure (l==[]);
            rewrite (pure (x == None)) as (is_list x []);
        }
        Some vl -> {
            rewrite (is_list_cases x l) as (is_list_cases (Some vl) l);
            unfold (is_list_cases (Some vl) l);
            intro_is_list_cons x vl;
        }
    }
}
```


```pulse
ghost
fn is_list_cases_none (#t:Type) (x:llist t) (#l:list t)
    requires is_list x l ** pure (x == None)
    ensures is_list x l ** pure (l == [])
{
    cases_of_is_list x l;
    rewrite (is_list_cases x l) as pure (l == []);
    intro_is_list_nil x;
}
```


```pulse
ghost
fn is_list_cases_some (#t:Type) (x:llist t) (v:node_ptr t) (#l:list t) 
    requires is_list x l ** pure (x == Some v)
    ensures exists* (node:node t) (tl:list t).
                pts_to v node **
                pure (l == node.head::tl) **
                is_list node.tail tl
{
    cases_of_is_list x l;
    rewrite (is_list_cases x l) as (is_list_cases (Some v) l);
    unfold (is_list_cases (Some v) l);
}
```

///////////////////////////////////////////////////////////////////////////////

```pulse
fn is_empty (#t:Type) (x:llist t) 
    requires is_list x 'l
    returns b:bool
    ensures is_list x 'l ** pure (b <==> ('l == []))
{
    match x {
        None -> {
            is_list_cases_none x;
            true
        }
        Some vl -> {
            is_list_cases_some x vl;
            intro_is_list_cons x vl;
            false
        }
    }
}
```

```pulse
fn rec length (#t:Type0) (x:llist t)
              (l:erased (list t))
    requires is_list x l
    returns n:nat
    ensures is_list x l ** pure (n == List.Tot.length l)
{
   match x {
    None -> {
        is_list_cases_none x;
        0
    }
    Some vl -> {
        is_list_cases_some x vl;
        let node = !vl;
        with tail tl. assert (is_list #t tail tl);
        rewrite each tail as node.tail; 
        let n = length #t node.tail tl;
        intro_is_list_cons x vl;
        (1 + n)
    }
   }
}
```

let null_llist #t : llist t = None #(node_ptr t)

```pulse
fn create (t:Type)
    requires emp
    returns x:llist t
    ensures is_list x []
{
    intro_is_list_nil #t null_llist;
    null_llist #t
}
```

```pulse
fn cons (#t:Type) (v:t) (x:llist t)
    requires is_list x 'l
    returns y:llist t
    ensures is_list y (v::'l)
{
    let y = alloc (mk_node v x);
    rewrite each x as (mk_node v x).tail in (is_list x 'l);
    intro_is_list_cons (Some y) y;
    Some y
}
```

```pulse
fn rec append (#t:Type0) (x y:llist t)
    requires is_list x 'l1 ** is_list y 'l2 ** pure (x =!= None)
    ensures is_list x (List.Tot.append 'l1 'l2)
{
   match x {
    None -> { //impossible
        drop (is_list y 'l2);
        drop (is_list x 'l1);
        elim_false (is_list x 'l1)
    }
    Some np -> {
        is_list_cases_some x np;
        let node = !np;
        with tail tl. assert (is_list #t tail tl);
        rewrite each tail as node.tail;
        match node.tail {
            None -> {
                is_list_cases_none node.tail;
                drop (is_list node.tail tl);
                np := mk_node node.head y;
                rewrite each y as (mk_node node.head y).tail in (is_list y 'l2);
                intro_is_list_cons x np; 
            }
            Some _ -> {
                append #t node.tail y #tl #'l2;
                intro_is_list_cons x np;
            }
        }
    }
   }
}
```

open Pulse.Lib.Stick

```pulse
ghost
fn intro_stick_aux (p:vprop) (u:unit)
    requires emp ** p
    ensures p
{
    ()
}
```

assume val dbg : vprop
```pulse
ghost
fn yields_idem (p:vprop)
   requires emp
   ensures p @==> p
{
   Pulse.Lib.Stick.intro_stick p p emp (intro_stick_aux p);
   fold (p @==> p);
}
```

```pulse
ghost
fn yields_curry (p q r:vprop)
   requires (p ** q) @==> r
   ensures p @==> (q @==> r)
{
//   intro_stick p (q @==> r) (p ** q @==> r)
//     ((_:unit) 
//     {
//         intro_stick q r
//             ((_:unit) 
//             {
//             yields_idem r;
//             })
//         })
//     })

    admit()
}
```

```pulse
ghost
fn yields_trans (p q r:vprop)
    requires (p @==> q) ** (q @==> r)
    ensures p @==> r
{
    admit()
}
```

```pulse
ghost
fn yields_comm_l (p q r:vprop)
   requires (p ** q) @==> r
   ensures (q ** p) @==> r
{
  admit()
}
```

```pulse
ghost
fn yields_assoc_l (p q r:vprop)
   requires (p ** (q ** r)) @==> r
   ensures ((p ** q) ** r) @==> r
{
  admit()
}
```


```pulse
ghost
fn elim_yields () (#p #q:vprop)
   requires (p @==> q) ** p
   ensures q
{
  unfold (p @==> q);
  elim_stick #emp_inames p q;
}
```

let assume_ (p:vprop) : stt_ghost unit emp_inames emp (fun _ -> p) = admit()
let not_null #t (x:llist t) : bool = Some? x

```pulse
ghost
fn yields_elim (#t:Type) 
               (v:node_ptr t)
               (n:node t)
               (tl:list t)
    requires 
        pts_to v n ** is_list n.tail tl
    ensures 
        is_list (Some v) (n.head::tl)
{
    intro_is_list_cons (Some v) v
}
```

assume
val yields_elim' (#t:Type) 
                 (v:node_ptr t)
                 (n:node t)
                 (tl:list t)
                 ()
   : stt_ghost unit emp_inames
        (pts_to v n ** is_list n.tail tl)
        (fun _ -> is_list (Some v) (n.head::tl))

```pulse
ghost
fn intro_yields_cons (#t:Type) 
                     (v:node_ptr t)
                     (#n:node t)
                     (#tl:erased (list t))
    requires 
        pts_to v n ** is_list n.tail tl
    ensures 
        is_list n.tail tl **
        (is_list n.tail tl @==> is_list (Some v) (n.head::tl))
{
    open Pulse.Lib.Stick;
    intro_stick #emp_inames _ _ _ 
                (yields_elim' #t v n tl);
    with p q. fold (p @==> q)
}
```

#push-options "--ext 'pulse:env_on_err'"
```pulse
fn length_iter (#t:Type) (x: llist t)
    requires is_list x 'l
    returns n:nat
    ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
    let mut cur = x;
    let mut ctr = 0; 
    yields_idem (is_list x 'l);
    while (
        with ll. assert pts_to cur ll;
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
        let n = !ctr;
        let ll = !cur;
        let node_ptr = Some?.v ll;
        with _ll suffix. assert (is_list #t _ll suffix);
        rewrite each _ll as ll;
        is_list_cases_some ll node_ptr;
        let node : node t = !node_ptr;
        with _node tl. assert (is_list #t _node.tail tl);
        rewrite (is_list #t _node.tail tl)
            as  (is_list node.tail tl);
        intro_yields_cons node_ptr;// #node #tl;
        // rewrite (yields (is_list node.tail tl) (is_list (Some node_ptr) (node.head::tl)))
        //     as  (yields (is_list node.tail tl) (is_list ll suffix));
        yields_trans (is_list node.tail tl) (is_list ll suffix) (is_list x 'l);
        cur := node.tail;
        ctr := n + 1;
    };
    with ll _sfx. assert (is_list #t ll _sfx);
    is_list_cases_none ll;
    // with p. rewrite (yields p (is_list x 'l)) as (yields (is_list #t ll []) (is_list x 'l));
    elim_yields ();
    let n = !ctr;
    n
}
```

```pulse
ghost
fn foo ()
  requires emp
  returns y:int
  ensures emp
{
  17
}
```
// let rec take (n:nat) (l:list 't { n < List.Tot.length l })
//   : list 'tg
//   = if n = 0 then []
//     else List.Tot.hd l :: take (n-1) (List.Tot.tl l)

//  let rec drop (n:nat) (l:list 't { n < List.Tot.length l })
//   : list 't
//   = if n = 0 then l
//     else drop (n-1) (List.Tot.tl l)
       
// ```pulse
// fn split (#t:Type) (x:llist t) (n:nat) (#l:(l:erased (list t) { n < List.Tot.length l }))
//     requires is_list x l
//     returns y:llist t
//     ensures is_list x (take n l) ** is_list y (drop n l)
// {
//     admit()
// }
// ```
