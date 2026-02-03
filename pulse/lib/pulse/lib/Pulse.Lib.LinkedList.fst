(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.LinkedList

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
open FStar.List.Tot
module T = Pulse.Lib.Trade.Util
module FA = Pulse.Lib.Forall.Util
module U32 = FStar.UInt32
open Pulse.Lib.BoundedIntegers
module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

noeq
type node (t:Type0) = {
    head : t;
    tail : option (node_ptr t);
}

and node_ptr (t:Type0) = box (node t)

and llist (t:Type0) = option (node_ptr t)

let rec is_list #t ([@@@mkey]x:llist t) (l:list t)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (x == None)
    | head::tl -> 
      exists* (v:node_ptr t) (tail:llist t).
        pure (x == Some v) **
        pts_to v { head; tail } **
        is_list tail tl

let is_list_cases #t ([@@@mkey]x:llist t) (l:list t)
  : Tot slprop
  = match x with
    | None -> pure (l == [])
    | Some v -> 
      exists* (n:node t) (tl:list t).
        pts_to v n **
        pure (l == n.head::tl) **
        is_list n.tail tl

ghost 
fn some_iff_cons #t (x:llist t) (#l:list t)
  requires is_list x l
  ensures  is_list x l ** pure (Some? x <==> Cons? l)
{
  match l {
    [] -> {
      unfold is_list;
      assert (pure (l == [])); (* Why is this needed? *)
      fold (is_list x []);
      ()
    }
    h::t -> {
      unfold is_list;
      fold (is_list x (h::t));
      ();
    }
  }
}

ghost
fn intro_is_list_cons (#t:Type0) (x:llist t) (v:node_ptr t) (#node:node t) (#tl:list t)
    requires pts_to v node ** is_list node.tail tl ** pure (x == Some v)
    ensures is_list x (node.head::tl)
{
  fold (is_list x (node.head::tl));
}

ghost
fn cases_of_is_list (#t:Type) (x:llist t) (l:list t)
    requires is_list x l
    ensures is_list_cases x l
{
    match l {
        [] -> {
            unfold (is_list x []);
            fold (is_list_cases None l);
            rewrite (is_list_cases None l) as (is_list_cases x l);
        }
        head :: tl -> {
            unfold (is_list x (head::tl));
            with w tail. _;
            let v = Some?.v x;
            rewrite each w as v;
            rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
            fold (is_list_cases (Some v) l);
            rewrite (is_list_cases (Some v) l) as
                    (is_list_cases x l)
        }
    }
}

ghost
fn is_list_of_cases (#t:Type) (x:llist t) (l:list t)
    requires is_list_cases x l
    ensures is_list x l
{
    match x {
        None -> { 
            unfold (is_list_cases None l);
            fold (is_list x []);
        }
        Some vl -> {
            unfold (is_list_cases (Some vl) l);
            intro_is_list_cons x vl;
        }
    }
}


ghost
fn is_list_cases_none (#t:Type) (x:llist t) (#l:list t)
    requires is_list x l ** pure (x == None)
    ensures  is_list x l ** pure (l == [])
{
  match l {
    Nil -> {
      ();
    }
    Cons _ _ -> {
      unfold is_list;
      assert (pure False); // NEEDED, bug? couldn't minimize easily
      unreachable ();
    }
  }
}

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


///////////////////////////////////////////////////////////////////////////////

fn is_empty (#t:Type) (x:llist t)
    requires is_list x 'l
    returns b:bool
    ensures is_list x 'l ** pure (b <==> ('l == []))
{
  match x {
    None -> {
      is_list_cases_none None;
      assert (pure ('l == []));
      rewrite (is_list None 'l) as (is_list x 'l);
      true
    }
    Some vl -> {
      is_list_cases_some (Some vl) vl;
      intro_is_list_cons x vl;
      false
    }
  }
}

fn head (#t:Type0) (x:llist t) (#l:erased (list t){Cons? l})
    requires is_list x l
    returns v:t
    ensures is_list x l ** pure (v == List.Tot.hd l)
{
  // Since Cons? l, we know x must be Some
  some_iff_cons x;
  let np = Some?.v x;
  is_list_cases_some x np;
  with node tl. _;
  let n = !np;
  // Restore the is_list predicate
  intro_is_list_cons x np;
  n.head
}

fn pop (#t:Type0) (x:llist t) (#l:erased (list t){Cons? l})
    requires is_list x l
    returns r:(llist t & t)
    ensures is_list (fst r) (List.Tot.tl l) ** pure (snd r == List.Tot.hd l)
{
  // Since Cons? l, we know x must be Some
  some_iff_cons x;
  let np = Some?.v x;
  is_list_cases_some x np;
  with node tl. _;
  let n = !np;
  let value = n.head;
  let next = n.tail;
  // Rewrite to connect the tail
  rewrite each node.tail as next;
  // Free the node
  Box.free np;
  // Return the tail and the value
  (next, value)
}

fn rec length (#t:Type0) (x:llist t)
              (#l:erased (list t))
    requires is_list x l
    returns n:nat
    ensures is_list x l ** pure (n == List.Tot.length l)
{
   match x {
    None -> {
        is_list_cases_none None;
        rewrite (is_list None l) as (is_list x l);
        0
    }
    Some vl -> {
        is_list_cases_some (Some vl) vl;
        with _node _tl. _;
        let node = !vl;
        let n = length node.tail;
        intro_is_list_cons x vl;
        (1 + n)
    }
   }
}

let null_llist #t : llist t = None #(node_ptr t)

fn create (t:Type)
    requires emp
    returns x:llist t
    ensures is_list x []
{
    fold (is_list null_llist ([] <: list t));
    null_llist #t
}



fn cons (#t:Type) (v:t) (x:llist t)
    requires is_list x 'l
    returns y:llist t
    ensures is_list y (v::'l)
{
    let y = Box.alloc { head=v; tail=x };
    rewrite each x as ({head=v; tail=x}).tail in (is_list x 'l);
    fold (is_list (Some y) (v::'l));
    Some y
}



fn rec append (#t:Type0) (x y:llist t)
  requires is_list x 'l1 ** (is_list y 'l2 ** pure (Cons? 'l1))
  ensures is_list x ('l1 @ 'l2)
{
  some_iff_cons x;
  let np = Some?.v x;
  is_list_cases_some x np;
  with _node _tl. _;
  let node = !np;
  let nt = node.tail;
  with tl. rewrite is_list node.tail tl as is_list nt tl;
  match nt {
    None -> {
      is_list_cases_none None;
      unfold (is_list #t None []);
      np := { node with tail = y };
      rewrite each y as ({ node with tail = y }).tail in (is_list y 'l2);
      intro_is_list_cons x np; 
    }
    Some p -> {
      some_iff_cons (Some p);
      append (Some p) y;
      rewrite each (Some p) as node.tail;
      intro_is_list_cons x np;
    }
  }
}


ghost
fn intro_yields_cons (#t:Type) 
                     (v:node_ptr t)
                     (#n:node t)
                     (#tl:erased (list t))
requires 
  pts_to v n **
  is_list n.tail tl //only there to enable inference of n and tl at call site
ensures 
  is_list n.tail tl **
  (is_list n.tail tl @==> is_list (Some v) (n.head::tl))
{
  intro (is_list n.tail tl @==> is_list (Some v) (n.head::tl)) #(v |-> n) fn _ {
    intro_is_list_cons (Some v) v
  }
}


fn move_next (#t:Type) (x:llist t)
    requires is_list x 'l ** pure (Cons? 'l)
    returns y:llist t
    ensures exists* tl.
        is_list y tl **
        (is_list y tl @==> is_list x 'l) **
        pure (Cons? 'l /\ tl == Cons?.tl 'l)
{ 
    some_iff_cons x;
    let np = Some?.v x;
    is_list_cases_some x np;
    let node = !np;
    intro_yields_cons np;
    rewrite each (Some np) as x;
    with tl. assert is_list node.tail tl;
    rewrite trade (is_list node.tail tl) (is_list x (node.head :: tl))
         as trade (is_list node.tail tl) (is_list x 'l);
    node.tail
}



fn length_iter (#t:Type) (x: llist t)
    requires is_list x 'l
    returns n:nat
    ensures is_list x 'l ** pure (n == List.Tot.length 'l)
{
  let mut cur = x;
  let mut ctr = 0; 
  T.refl (is_list x 'l);
  while (
    let v = Pulse.Lib.Reference.(!cur); 
    Some? v
  )
  invariant
  exists* (n:int) ll suffix.
    pts_to ctr n **
    pts_to cur ll **
    is_list ll suffix **
    (is_list ll suffix @==> is_list x 'l) **
    pure (
        List.Tot.length 'l >= List.Tot.length suffix /\
        n == List.Tot.length 'l - List.Tot.length suffix)
    (* ^ Having the bounded_int nat instance in BoundedIntegers means we try to
    to check the subtraction as a nat, which fails without the extra condition.
    We can also just write `n + len suff = len 'l`. *)
  {
    with _n _ll suffix. _;
    let n = Pulse.Lib.Reference.(!ctr);
    let ll = Pulse.Lib.Reference.(!cur);
    some_iff_cons ll;
    let next = move_next ll;
    with tl. assert (is_list next tl);
    T.trans (is_list next tl) (is_list ll suffix) (is_list x 'l);
    Pulse.Lib.Reference.(cur := next);
    Pulse.Lib.Reference.(ctr := n + 1);
  };
  with _n ll _sfx. _;
  is_list_cases_none ll;
  T.elim _ _;
  let n = Pulse.Lib.Reference.(!ctr);
  n
}



fn is_last_cell (#t:Type) (x:llist t)
    requires is_list x 'l ** pure (Cons? 'l)
    returns b:bool
    ensures is_list x 'l ** pure (b == (List.Tot.length 'l = 1))
{
  some_iff_cons x;
  let np = Some?.v x;
  is_list_cases_some x np;
  let node = !np;
  let nt = node.tail;
  with tl. rewrite is_list node.tail tl as is_list nt tl;
  match nt {
    None -> {
      is_list_cases_none None;
      with tl. rewrite is_list #t None tl as is_list node.tail tl;
      intro_is_list_cons x np;
      true
    }
    Some vtl -> {
      rewrite each Some vtl as node.tail;
      is_list_cases_some node.tail vtl;
      intro_is_list_cons node.tail vtl;
      intro_is_list_cons x np;
      false
    }
  }
}

fn append_at_last_cell (#t:Type) (x y:llist t)
requires
  is_list x 'l1 **
  is_list y 'l2 **
  pure (List.Tot.length 'l1 == 1)
ensures
  is_list x (List.Tot.append 'l1 'l2)
{
  some_iff_cons x;
  let np = Some?.v x;
  is_list_cases_some x np;
  let node = !np;
  let nt = node.tail;
  with tl. rewrite is_list node.tail tl as is_list nt tl;
  match nt {
    None -> {
      is_list_cases_none None;
      unfold (is_list #t None []);
      np := { node with tail = y };
      rewrite each y as ({node with tail = y}).tail in (is_list y 'l2);
      intro_is_list_cons x np; 
    }
    Some vtl -> {
      is_list_cases_some (Some vtl) vtl;
      unreachable ();
    }
  }
}

ghost
fn non_empty_list (#t:Type0) (x:llist t)
    requires is_list x 'l ** pure (Cons? 'l)
    ensures is_list x 'l ** pure (Some? x)
{
    unfold (is_list x (Cons?.hd 'l :: Cons?.tl 'l));
    with v tail. _;
    with n tl. assert (pts_to v n ** is_list tail tl);
    rewrite each tail as n.tail;
    intro_is_list_cons x v #n #tl;
}

let is_cons #t ([@@@mkey] x: list t) hd tl = pure (x == hd :: tl)

fn move_next_forall (#t:Type) (x:llist t)
    requires is_list x 'l ** pure (Some? x)
    returns y:llist t
    ensures exists* hd tl.
        is_list y tl **
        (forall* tl'. is_list y tl' @==> is_list x (hd::tl')) **
        is_cons 'l hd tl
{ 
    let np = Some?.v x;
    is_list_cases_some x np;
    let node = !np;
    intro (forall* tl'. is_list node.tail tl' @==> is_list x (node.head::tl')) #(np |-> node) fn _ tl' {
      intro_is_list_cons x np;
    };
    with tl. assert is_list node.tail tl;
    fold is_cons 'l node.head tl;
    node.tail
}


let append_assoc_singleton (l1 l2:list 'a) (x:'a) 
: Lemma 
    (ensures l1@(x::l2) == (l1 @ [x])@l2)
    [SMTPat (l1@(x::l2))]
= List.Tot.Properties.append_assoc l1 [x] l2

fn not_is_last_cell (#t:Type) (x:llist t)
    preserves is_list x 'l
    requires pure (Cons? 'l)
    returns b:bool
    ensures pure (b == (List.Tot.length 'l <> 1))
{
  not (is_last_cell x)
}

fn append_iter (#t:Type) (x y:llist t)
  requires is_list x 'l1 ** is_list y 'l2 ** pure (Cons? 'l1)
  ensures is_list x ('l1 @ 'l2)
{
  let mut cur = x;
  (* the base case, set up the initial invariant *)
  intro (forall* l. is_list x l @==> is_list x ([]@l)) fn _ _{};
  while (not_is_last_cell Pulse.Lib.Reference.(!cur))
    invariant exists* ll pfx sfx.
      (cur |-> ll) **
      is_list ll sfx **
      (forall* sfx'. is_list ll sfx' @==> is_list x (pfx @ sfx')) **
      pure (pfx @ sfx == 'l1 /\ Cons? sfx)
  {
    with ll pfx sfx. _;
    some_iff_cons ll;
    let next = move_next_forall Pulse.Lib.Reference.(!cur);
    with hd tl. unfold is_cons sfx hd tl;
    (* this is the key induction step *)
    FA.trans_compose
        (is_list next) (is_list ll) (is_list x)
        (fun tl -> reveal hd :: tl)
        (fun tl -> pfx @ tl);
    rewrite (forall* tl. is_list next tl @==> is_list x (pfx@(reveal hd::tl)))
          as (forall* tl. is_list next tl @==> is_list x ((pfx@[reveal hd])@tl));
    Pulse.Lib.Reference.(cur := next);
  };
  with ll pfx sfx. _;
  append_at_last_cell Pulse.Lib.Reference.(!cur) y;
  (* finally, use the quqnatified postcondition of the invariant *)
  FA.elim_forall_imp (is_list ll) (fun sfx' -> is_list x (pfx @ sfx')) (sfx@'l2);
  List.Tot.Properties.append_assoc pfx sfx 'l2;
}


fn detach_next (#t:Type) (x:llist t)
  requires is_list x 'l ** pure (Cons? 'l)
  returns y:llist t
  ensures exists* hd tl.
    is_list x [hd] **
    is_list y tl **
    pure ('l == hd::tl)
{
  some_iff_cons x;
  let v = Some?.v x;
  is_list_cases_some x v;
  with node tl. _;
  let nodev = !v;
  let node' = { nodev with tail = None};
  fold (is_list node'.tail []);
  v := node';
  intro_is_list_cons x v;
  nodev.tail
}


fn split (#t:Type0) (x:llist t) (n:U32.t) (#xl:erased (list t))
 requires is_list x xl ** pure (Cons? xl /\ 0 < v n /\ v n <= List.Tot.length xl)
 returns  y:llist t
 ensures exists* l1 l2. 
    is_list x l1 **
    is_list y l2 **
    pure (xl == l1 @ l2 /\
          List.Tot.length l1 == v n)
 {
  some_iff_cons x;
  let mut cur = x;
  let mut ctr = 0ul;
  (* the base case, set up the initial invariant *)
  intro (forall* l. is_list x l @==> is_list x ([]@l)) fn _ _{};
  while (Pulse.Lib.Reference.(!ctr) <> (n - 1ul))
    invariant exists* i ll pfx sfx.
      pts_to ctr i **
      pts_to cur ll **
      is_list ll sfx **
      (forall* sfx'. is_list ll sfx' @==> is_list x (pfx @ sfx')) **
      pure (
         v i == List.Tot.length pfx /\
         i <= n - 1ul /\
         Some? ll /\
         pfx@sfx == xl
      )
  {
    with i ll pfx sfx. _;
    let next = move_next_forall Pulse.Lib.Reference.(!cur);
    with hd tl. unfold is_cons sfx hd tl;
    (* this is the key induction step *)
    FA.trans_compose
        (is_list next) (is_list ll) (is_list x)
        (fun tl -> hd :: tl)
        (fun tl -> pfx @ tl);
    rewrite (forall* tl. is_list next tl @==> is_list x (pfx@(hd::tl)))
          as (forall* tl. is_list next tl @==> is_list x ((pfx@[hd])@tl));
    Pulse.Lib.Reference.(cur := next);
    Pulse.Lib.Reference.(ctr := !(ctr) + 1ul);
    List.Tot.append_length pfx [hd];
    non_empty_list next; (* need to prove Some? next *)
  };
  with i ll pfx sfx. _;
  let last = Pulse.Lib.Reference.(!cur);
  let y = detach_next last;
  with hd tl. _;
  FA.elim_forall_imp (is_list last) (fun sfx' -> is_list x (pfx @ sfx')) [hd];
  List.Tot.append_length pfx [hd];
  y
 }

fn insert (#kk:Type0) (x:llist kk) (item:kk) (pos:U32.t) (#xl:erased (list kk))
  requires is_list x xl ** pure (Cons? xl /\ 0 < v pos /\ v pos < List.Tot.length xl)
  ensures exists* l0 l1.
  is_list x (l0 @ item :: l1) **
  pure (
      xl == l0 @ l1 /\
      List.Tot.length l0 == v pos
    )
{
  let y = split x pos;
  with l0 l1. _;
  let z = cons item y;
  append x z;
  with m. rewrite (is_list x m) as (is_list x (l0 @ item :: l1));
}



fn delete (#kk:Type0) (x:llist kk) (item:kk) (pos:U32.t) (#xl:erased (list kk))
  requires is_list x xl ** pure (Cons? xl /\ 0 < v pos /\ v pos < List.Tot.length xl)
  ensures exists* l0 l1.
  is_list x (l0 @ item :: l1) **
  pure (
      xl == l0 @ l1 /\
      List.Tot.length l0 == v pos
    )
{
  let y = split x pos;
  with l0 l1. _;
  let z = cons item y;
  append x z;
  with m. rewrite (is_list x m) as (is_list x (l0 @ item :: l1));
}
