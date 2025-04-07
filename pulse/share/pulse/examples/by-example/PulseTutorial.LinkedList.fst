(*
   Copyright 2024 Microsoft Research

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


module PulseTutorial.LinkedList
#lang-pulse
open Pulse.Lib.Pervasives
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
//end llist$

//is_list$
let rec is_list #t (x:llist t) (l:list t)
: Tot slprop (decreases l)
= match l with
  | [] -> pure (x == None)
  | head::tl -> 
    exists* (p:node_ptr t) (tail:llist t).
      pure (x == Some p) **
      pts_to p { head; tail } **
      is_list tail tl
//end is_list$

//boilerplate$

ghost
fn elim_is_list_nil (#t:Type0) (x:llist t)
requires is_list x 'l ** pure ('l == [])
ensures pure (x == None)
{
   rewrite each 'l as Nil #t;
   unfold (is_list x [])
}



ghost
fn intro_is_list_nil (#t:Type0) (x:llist t)
requires pure (x == None)
ensures is_list x []
{
    fold (is_list x []);
}



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
  unfold (is_list x (head::tl));
}

    


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
    fold (is_list x (node.head::tl));
}

//end boilerplate$

//is_list_cases$
let is_list_cases #t (x:llist t) (l:list t)
: slprop 
= match x with
  | None -> pure (l == [])
  | Some v -> 
    exists* (n:node t) (tl:list t).
      pts_to v n **
      pure (l == n.head::tl) **
      is_list n.tail tl
//end is_list_cases$

//cases_of_is_list$
ghost
fn cases_of_is_list #t (x:llist t) (l:list t)
requires is_list x l
ensures is_list_cases x l
{
  match l {
    [] -> {
      unfold (is_list x []);
      fold (is_list_cases None l);
      rewrite each (None #(ref (node t))) as x;
    }
    head :: tl -> {
      unfold (is_list x (head::tl));
      with w tail. _;
      let v = Some?.v x;
      rewrite each w as v;
      rewrite each tail as (({ head; tail }).tail) in (is_list tail tl);
      fold (is_list_cases (Some v) l);
      rewrite each (Some #(ref (node t)) v) as x;
    }
  }
}
//end cases_of_is_list$


//is_list_case_none$
ghost
fn is_list_case_none (#t:Type) (x:llist t) (#l:list t)
requires is_list x l ** pure (x == None)
ensures is_list x l ** pure (l == [])
{
  cases_of_is_list x l;
  rewrite each x as (None #(ref (node t)));
  unfold (is_list_cases None l);
  fold (is_list x []);
}
//end is_list_case_none$


//is_list_case_some$
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
//end is_list_case_some$



//length$
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
      let node = !vl;
      let n = length node.tail;
      intro_is_list_cons x vl;
      (1 + n)
    }
  }
}
//end length$



//length_tail$
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
      with _node _tl. _;
      let n = !vl;
      rewrite each _node as n;
      let n = length_tail n.tail (1 + k);
      intro_is_list_cons x vl;
      n
    }
  }
}
//end length_tail$


module I = Pulse.Lib.Trade.Util
open I

//tail_for_cons$
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
//end tail_for_cons$

//tail$
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
    rewrite each node as nd;
    tail_for_cons np tl;
    nd.tail
}
//end tail$

//length_iter$
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
    let v = !cur;
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
    I.trans (is_list next tl) _ _; //extend the trade, transitively
    cur := next;
    ctr := n + 1;
  };
  with _n ll _sfx. _;
  is_list_case_none ll; //this tells us that suffix=[]; so n == List.Tot.length 'l
  I.elim _ _;           //regain ownership of x, giving up ll
  let n = !ctr;
  n
}
//end length_iter$

//append$
fn rec append (#t:Type0) (x y:llist t)
requires is_list x 'l1 ** is_list y 'l2 ** pure (Some? x)
ensures is_list x ('l1 @ 'l2)
{
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  let node = !np;
  rewrite each _node as node;
  match node.tail {
    None -> {
      is_list_case_none None;
      elim_is_list_nil None;
      np := { node with tail = y };
      rewrite each y as ({ node with tail = y }).tail in (is_list y 'l2);
      intro_is_list_cons x np; 
    }
    Some _ -> {
      append node.tail y;
      intro_is_list_cons x np;
    }
  }
}
//end append$

//tail_alt$
fn tail_alt (#t:Type) (x:llist t)
requires is_list x 'l ** pure (Some? x)
returns y:llist t
ensures exists* hd tl.
  is_list y tl **
  (forall* tl'. is_list y tl' @==> is_list x (hd::tl')) **
  pure ('l == hd::tl)
{ 
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  let node = !np;
  rewrite each _node as node;
  ghost
  fn aux (tl':list t)
    requires pts_to np node ** is_list node.tail tl'
    ensures is_list x (node.head::tl')
  {
    intro_is_list_cons x np;
  };
  FA.intro_forall_imp _ _ _ aux;
  node.tail
}
//end tail_alt$

//is_last_cell$
fn is_last_cell (#t:Type) (x:llist t)
requires is_list x 'l ** pure (Some? x)
returns b:bool
ensures is_list x 'l ** pure (b == (List.Tot.length 'l = 1))
{
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  let node = !np;
  rewrite each _node as node;
  match node.tail {
    None -> { 
      is_list_case_none node.tail;
      intro_is_list_cons x np;
      true
    }
    Some vtl -> { 
      is_list_case_some node.tail vtl;
      intro_is_list_cons node.tail vtl;
      intro_is_list_cons x np;
      false
    }
  }
}
//end is_last_cell$

//append_at_last_cell$
fn append_at_last_cell (#t:Type) (x y:llist t)
requires
  is_list x 'l1 **
  is_list y 'l2 **
  pure (Some? x /\ List.Tot.length 'l1 == 1)
ensures
  is_list x (List.Tot.append 'l1 'l2)
{
  let np = Some?.v x;
  is_list_case_some x np;
  with _node _tl. _;
  elim_is_list_nil _node.tail;
  let node = !np;
  np := { node with tail = y };
  rewrite each y as ({node with tail = y}).tail in (is_list y 'l2);
  intro_is_list_cons x np; 
}
//end append_at_last_cell$

//non_empty_list$
ghost
fn non_empty_list (#t:Type0) (x:llist t)
requires is_list x 'l ** pure (Cons? 'l)
ensures is_list x 'l ** pure (Some? x)
{
    elim_is_list_cons x _ (Cons?.hd 'l) (Cons?.tl 'l);
    with v tail. _;
    with n tl. assert (pts_to v n ** is_list tail tl);
    rewrite each tail as n.tail;
    intro_is_list_cons x v #n #tl;
}
//end non_empty_list$

//append_iter$
fn append_iter (#t:Type) (x y:llist t)
requires is_list x 'l1 ** is_list y 'l2 ** pure (Some? x)
ensures is_list x ('l1 @ 'l2)
{
  let mut cur = x;
  //the base case, set up the initial invariant
  FA.intro emp (fun l -> I.refl #[] (is_list x l));
  rewrite (forall* l. is_list x l @==> is_list x l)
      as  (forall* l. is_list x l @==> is_list x ([]@l));
  while (
    with _b ll pfx sfx. _;
    let l = !cur;
    rewrite each ll as l;
    let b = is_last_cell l; //check if we are at the last cell
    if b 
    { 
      false //yes, break out of the loop
    }
    else 
    {
      let next = tail_alt l;
      with hd tl. _;
      (* this is the key induction step *)
      FA.trans_compose 
          (is_list next) (is_list l) (is_list x)
          (fun tl -> hd :: tl)
          (fun tl -> pfx @ tl);
      //Use F* sugar for classical connectives to introduce a property
      //needed for the next rewrite
      (introduce forall tl. pfx @ (hd :: tl) == (pfx @ [hd]) @ tl
       with List.Tot.Properties.append_assoc pfx [hd] tl);
      rewrite (forall* tl. is_list next tl @==> is_list x (pfx@(hd::tl)))
           as (forall* tl. is_list next tl @==> is_list x ((pfx@[hd])@tl));
      cur := next;
      non_empty_list next; //need to prove that Some? next, for the invariant
      true
    }
  )
  invariant b.
  exists* ll pfx sfx.
    pts_to cur ll **   //cur holds the pointer to the current head of the traversal, ll
    is_list ll sfx **  //ll points to some suffix of the original list, since `pfx@sfx = 'l1` below
    //the main bit: whatever ll points to `sfx'`, trade it for x pointing to the concatenation ``pfx @ sfx'`` 
    (forall* sfx'. is_list ll sfx' @==> is_list x (pfx @ sfx')) ** 
    pure (
      (b==false ==> List.Tot.length sfx == 1) /\ //the loop ends when we reach the last cell
      pfx@sfx == 'l1 /\ //sfx is really the suffix
      Some? ll          //and the current list is always non-null
    )
  { () };
  with ll pfx sfx. _;
  let last = !cur;
  rewrite each ll as last;
  append_at_last_cell last y;
  FA.elim_forall_imp (is_list last) (fun sfx' -> is_list x (pfx @ sfx')) (sfx@'l2);
  List.Tot.Properties.append_assoc pfx sfx 'l2;
  ()
}
//end append_iter$