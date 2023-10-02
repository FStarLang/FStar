module Pulse.Lib.LinkedList
open Pulse.Lib.Pervasives

noeq
type ll (t:Type0) = {
    head : t;
    tail : llist t;
}

and llist (t:Type0) = ref (option (ll t))

let mk_ll #t (hd:t) (tl:llist t) : Tot (ll t)
  = {head=hd; tail=tl}

let rec is_list #t (x:llist t) (l:list t)
  : Tot vprop (decreases l)
  = match l with
    | [] -> pts_to x None
    | head::tl -> 
     exists_ (fun (tail:llist t) -> 
        pts_to x (Some (mk_ll head tail)) **
        is_list tail tl
    )

let is_list_cases_opt #t (x:llist t) (l:list t) (v:option (ll t)) =
    match v with
    | None -> pure (l == [])
    | Some v -> 
        exists_ (fun (tl:list t) ->
            pure (l == v.head::tl) **
            is_list v.tail tl
             )


let is_list_cases #t (x:llist t) (l:list t)
  : Tot vprop 
  = exists_ (fun (v:option (ll t)) ->
     pts_to x v **
     is_list_cases_opt x l v)

//open FStar.Tactics
module T = FStar.Tactics


let unfold_is_list_cons #t (x:llist t) (head:t) (tl:list t)
  : Lemma (is_list x (head::tl) ==
            (exists_ (fun (tail:llist t) -> 
                pts_to x #full_perm (Some (mk_ll head tail)) **
                is_list tail tl
            )))
  = assert (is_list x (head::tl) ==
            (exists_ (fun (tail:llist t) -> 
                pts_to x #full_perm (Some (mk_ll head tail)) **
                is_list tail tl)))
    by (T.trefl())

```pulse
ghost
fn elim_is_list_nil (#t:Type0) (x:llist t) 
  requires is_list x []
  ensures pts_to x None
{
   unfold (is_list x [])
}
```

```pulse
ghost
fn intro_is_list_nil (#t:Type0) (x:llist t)
    requires pts_to x None
    ensures is_list x []
{
    fold (is_list x [])
}
```

```pulse
ghost
fn elim_is_list_cons (#t:Type0) (x:llist t) (hd:t) (tl:list t)
  requires is_list x (hd::tl)
  ensures exists (tail:llist t). pts_to x (Some (mk_ll hd tail)) ** is_list tail tl
{
//   rewrite (is_list x (hd::tl))
//     as exists (tail:llist t). pts_to x (Some (mk_ll hd tail)) ** is_list tail tl
//     (by T.norm ())
    admit()
}
```

```pulse
ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (tail:llist t) (#hd:t) (#tl:list t)
    requires pts_to x (Some (mk_ll hd tail)) ** is_list tail tl
    ensures is_list x (hd::tl)
{
    // rewrite (exists (tail:llist t). 
    //             pts_to x (Some (mk_ll hd tail)) **
    //             is_list tail tl)
    //   as is_list x (hd::tl);
    admit()
}
```


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
      fold (is_list_cases_opt x l None);
      fold (is_list_cases x l);
    }
    Cons head tl -> { 
      rewrite (is_list x l) as (is_list x (head::tl));
      elim_is_list_cons x head tl;
      with tail. assert is_list tail tl;   
      let v = mk_ll head tail;
      rewrite (is_list tail tl) as (is_list v.tail tl);
      fold (is_list_cases_opt x l (Some v));
      fold (is_list_cases x l);
    }
    }
}
```

```pulse
ghost
fn is_list_of_cases (#t:Type) (x:llist t) (l:list t) (v:option (ll t))
    requires pts_to x v ** is_list_cases_opt x l v
    ensures is_list x l
{
    match v {
    None -> { 
      rewrite (is_list_cases_opt x l v) as (pure (l==[]));
      rewrite (pts_to x v) as (is_list x l);
    }
    Some vl -> {
      rewrite (is_list_cases_opt x l v) as
              (is_list_cases_opt x l (Some vl));
      unfold  (is_list_cases_opt x l (Some vl));
      with tl. assert is_list vl.tail tl;
      assert pure (l == vl.head::tl);
      rewrite (pts_to x v) as (pts_to x (Some (mk_ll vl.head vl.tail)));
      intro_is_list_cons x vl.tail;
    }
    }
}
```

```pulse
fn read_head (#t:Type) (x:llist t) (#l:erased (list t))
    requires is_list x l
    returns v:option (ll t)
    ensures pts_to x v ** is_list_cases_opt x l v
{
    cases_of_is_list x l;
    unfold (is_list_cases x l);
    let v = !x;
    v
}
```

```pulse
ghost
fn is_list_cases_none (#t:Type) (x:llist t) (#l:list t) (#v:option (ll t))
    requires is_list_cases_opt x l v ** pure (v == None)
    ensures pure (l == [])
{
    rewrite (is_list_cases_opt x l v) as
            (is_list_cases_opt x l None);
    unfold (is_list_cases_opt x l None)
}
```

```pulse
ghost
fn is_list_cases_some (#t:Type) (x:llist t) (v:ll t) (#l:list t)
    requires is_list_cases_opt x l (Some v)
    ensures  exists (tl:list t).
                pure (l == v.head::tl) **
                is_list v.tail tl
{
    unfold (is_list_cases_opt x l (Some v));
}
```

```pulse
fn is_empty (#t:Type) (x:llist t) 
    requires is_list x 'l
    returns b:bool
    ensures is_list x 'l ** pure (b <==> ('l == []))
{
    let v = read_head x;
    match v {
        None -> {
            is_list_cases_none x;
            intro_is_list_nil x;
            true
        }
        Some vl -> {
            is_list_cases_some x vl;
            intro_is_list_cons x vl.tail #vl.head;
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
   let v = read_head x;
   match v {
    None -> {
        is_list_cases_none x;
        intro_is_list_nil x;
        0
    }
    Some vl -> {
        is_list_cases_some x vl;
        with tl. assert is_list vl.tail tl;
        let n = perform (length_rec vl.tail tl);
        intro_is_list_cons x vl.tail #vl.head;
        (1 + n)
    }
   }
}
```

```pulse
fn create (t:Type)
    requires emp
    returns x:llist t
    ensures is_list x []
{
    let x = alloc #(option (ll t)) None;
    intro_is_list_nil x;
    x
}
```

```pulse
fn cons (#t:Type) (v:t) (x:llist t)
    requires is_list x 'l
    returns y:llist t
    ensures is_list y (v::'l)
{
    let y = alloc #(option (ll t)) (Some (mk_ll v x));
    intro_is_list_cons y x;
    y
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
    requires is_list x 'l1 ** is_list y 'l2 
    ensures is_list x (List.Tot.append 'l1 'l2)
{
   let vx = read_head x;
   match vx {
    None -> {
        is_list_cases_none x; 
        let vy = read_head y;
        free y;
        match vy {
            None -> {
                is_list_cases_none y;
                intro_is_list_nil x;
            }
            Some vly -> {
                is_list_cases_some y vly;
                x := Some vly;
                rewrite (pts_to x (Some vly))
                    as  (pts_to x (Some (mk_ll vly.head vly.tail)));
                intro_is_list_cons x vly.tail;
            }
        }
    }
    Some vl -> {
        is_list_cases_some x vl;
        with tl. assert is_list vl.tail tl;
        perform (append_rec vl.tail y tl 'l2);
        intro_is_list_cons x vl.tail #vl.head;
    }
   }
}
```

let rec take (n:nat) (l:list 't { n < List.Tot.length l })
  : list 't
  = if n = 0 then []
    else List.Tot.hd l :: take (n-1) (List.Tot.tl l)

 let rec drop (n:nat) (l:list 't { n < List.Tot.length l })
  : list 't
  = if n = 0 then l
    else drop (n-1) (List.Tot.tl l)
       
```pulse
fn split (#t:Type) (x:llist t) (n:nat) (#l:(l:erased (list t) { n < List.Tot.length l }))
    requires is_list x l
    returns y:llist t
    ensures is_list x (take n l) ** is_list y (drop n l)
{
    admit()
}
```