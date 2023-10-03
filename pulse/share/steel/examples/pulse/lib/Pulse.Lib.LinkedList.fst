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
      exists_ (fun (v:node_ptr t) ->
      exists_ (fun (tail:llist t) ->
        pure (x == Some v) **
        pts_to v (mk_node head tail) **
        is_list tail tl
    ))


let is_list_cases #t (x:llist t) (l:list t)
  : Tot vprop 
  = match x with
    | None -> pure (l == [])
    | Some v -> 
      exists_ (fun (n:node t) ->
      exists_ (fun (tl:list t) ->
        pts_to v n **
        pure (l == n.head::tl) **
        is_list n.tail tl
      ))



let unfold_is_list_cons #t (x:llist t) (head:t) (tl:list t)
  :  Lemma (is_list x (head::tl) ==
            exists_ (fun (v:node_ptr t) ->
                exists_ (fun (tail:llist t) ->
                    pure (x == Some v) **
                    pts_to v (mk_node head tail) **
                    is_list tail tl
                )))
  = assert (is_list x (head::tl) ==
            exists_ (fun (v:node_ptr t) ->
                exists_ (fun (tail:llist t) ->
                    pure (x == Some v) **
                    pts_to v (mk_node head tail) **
                    is_list tail tl
                )))
    by (T.norm [delta_only [`%is_list]; zeta;iota]; T.dump "A") //trefl())

```pulse
ghost
fn elim_is_list_nil (#t:Type0) (x:llist t) 
  requires is_list x []
  ensures pure(x == None)
{
   rewrite (is_list x []) as pure (x == None)
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

```pulse
ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (head:t) (tl:list t)
  requires is_list x (head::tl)
  ensures exists (v:node_ptr t) (tail:llist t).
            pure (x == Some v) **
            pts_to v (mk_node head tail) **
            is_list tail tl
{
//   rewrite (is_list x (hd::tl))
//     as exists (tail:llist t). pts_to x (Some (mk_ll hd tail)) ** is_list tail tl
//     (by T.norm ())
    //unfold (is_list #t x (head::tl));
    admit()
}
```

```pulse
ghost
fn intro_is_list_cons (#t:Type0) (v:node_ptr t) (#tail:llist t) (#hd:t) (#tl:list t)
    requires pts_to v (mk_node hd tail) ** is_list tail tl
    ensures is_list (Some v) (hd::tl)
{
//     assert (exists (v:node_ptr t) (tail:llist t).
//         pure (Some v == Some v) **
//         pts_to v (mk_node hd tail) **
//         is_list tail tl);
    admit()
//    fold // [iota] 
//      (is_list (Some v) (hd::tl))
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
            with n. assert (pts_to vl n);
            with tl. assert (is_list n.tail tl);
            rewrite (pts_to vl n) as (pts_to vl (mk_node n.head n.tail));
            intro_is_list_cons vl;
            rewrite (is_list (Some vl) (n.head::tl)) as (is_list x l);
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
    ensures exists (hd:t) (tail:llist t) (tl:list t).
                pts_to v (mk_node hd tail) **
                pure (l == hd::tl) **
                is_list tail tl
{
    cases_of_is_list x l;
    rewrite (is_list_cases x l) as (is_list_cases (Some v) l);
    unfold (is_list_cases (Some v) l);
    with n. rewrite (pts_to v n) as (pts_to v (mk_node #t n.head n.tail));
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
            intro_is_list_cons vl;
            rewrite (is_list (Some vl) 'l) as (is_list x 'l);
            false
        }
    }
}
```

let perform (#a:Type0) (#p:vprop) (#q:a -> vprop)
            (f: stt a p q)
  : stt a p q = f  

```pulse
fn length (#t:Type) (x:llist t)
          (length_rec: 
            (y:llist t ->
             m:erased (list t) ->
             stt nat
                 (is_list y m)
                 (fun n -> is_list y m ** pure (n == List.Tot.length m))))
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
        rewrite (is_list tail tl) as (is_list #t node.tail tl);
        let n = perform (length_rec node.tail tl);
        rewrite (pts_to vl node) as (pts_to vl (mk_node node.head node.tail));
        intro_is_list_cons vl;
        rewrite (is_list (Some vl) l) as (is_list x l);
        (1 + n)
    }
   }
}
```

let return (#t:Type) (x:t) : stt t emp (fun y -> pure (x == y)) = admit()
let null_llist #t : llist t = None #(node_ptr t)

assume val dbg : vprop

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
    intro_is_list_cons y;
    Some y
}
```

```pulse
fn append (#t:Type) (x y:llist t)
          (append_rec : 
            (x:llist t ->
             y:llist t ->
             m:erased (list t) ->
             n:erased (list t) ->
             stt unit
                 (is_list x m ** is_list y n)
                 (fun _ -> is_list x (List.Tot.append m n))))
    requires is_list x 'l1 ** is_list y 'l2 ** pure (x =!= None)
    ensures is_list x (List.Tot.append 'l1 'l2)
{
   match x {
    None -> { //impossible
        drop (is_list y 'l2)
    }
    Some np -> {
        is_list_cases_some x np;
        let node = !np;
        with tail tl. assert (is_list #t tail tl);
        rewrite (pts_to np node) as (pts_to np (mk_node node.head node.tail));
        rewrite (is_list tail tl) as (is_list #t node.tail tl);
        match node.tail {
            None -> {
                is_list_cases_none node.tail;
                drop (is_list node.tail tl);
                np := mk_node node.head y;
                intro_is_list_cons np #y;
                with l. rewrite (is_list (Some np) l) as (is_list x l);
            }
            Some _ -> {
                perform (append_rec node.tail y tl 'l2);
                intro_is_list_cons np;
                with l. rewrite (is_list (Some np) l) as (is_list x l);
            }
        }
    }
   }
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