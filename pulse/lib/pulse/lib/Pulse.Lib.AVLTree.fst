(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Sheera Shamsu
*)
//Pulse AVL tree implementation. Inspired from Steel. The FStar spec file is adopted from Steel
//----------------------------------------------------------------------------------------------------------
module Pulse.Lib.AVLTree
#lang-pulse
open Pulse.Lib.Pervasives

module T = Pulse.Lib.Spec.AVLTree

module Box = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }

noeq
type node (t:Type0) = {
    data : t;
    left : tree_t t;
    right : tree_t t;
}

and node_ptr (t:Type0) = box (node t)

//A nullable pointer to a node
and tree_t (t:Type0) = option (node_ptr t)

let rec is_tree #t ct ft = match ft with
  | T.Leaf -> pure (ct == None)
  | T.Node data left' right' ->
    exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
      pure (ct == Some p) **
      (p |-> { data = data ; left = lct ; right = rct}) **
      is_tree lct left' **
      is_tree rct right'


ghost
fn elim_is_tree_leaf (#t:Type0) (x:tree_t t)
  requires is_tree x T.Leaf
  ensures pure (x == None)
{
   unfold (is_tree x T.Leaf) 
}



ghost
fn intro_is_tree_leaf (#t:Type0) (x:tree_t t) 
  requires pure (x == None)
  ensures is_tree x T.Leaf
{
  fold (is_tree x T.Leaf); 
}



ghost
fn elim_is_tree_node (#t:Type0) (ct:tree_t t) (data:t) (ltree:T.tree t) (rtree:T.tree t)
  requires is_tree ct (T.Node data ltree rtree)
  ensures (
  exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
    pure (ct == Some p) **
    (p |-> { data; left = lct;right = rct }) **
    is_tree lct ltree **
    is_tree rct rtree
)
{
  unfold is_tree
}


module G = FStar.Ghost


ghost
fn intro_is_tree_node (#t:Type0) (ct:tree_t t) (v:node_ptr t) (#node:node t) (#ltree:T.tree t) (#rtree:T.tree t)
requires
  (v |-> node) **
  is_tree node.left ltree **
  is_tree node.right rtree **
  pure (ct == Some v)
ensures
  is_tree ct (T.Node node.data ltree rtree)
{
  fold (is_tree ct (T.Node node.data ltree rtree))
}


[@@no_mkeys] // internal only
let is_tree_cases #t (x : option (box (node t))) (ft : T.tree t)
= match x with
  | None -> pure (ft == T.Leaf)
  | Some v -> 
    exists* (n:node t) (ltree:T.tree t) (rtree:T.tree t).
      (v |-> n) **
      pure (ft == T.Node n.data ltree rtree) **
      is_tree n.left ltree **
      is_tree n.right rtree

ghost
fn cases_of_is_tree #t (x:tree_t t) (ft:T.tree t)
  requires is_tree x ft
  ensures  is_tree_cases x ft
{
  match ft {
    T.Leaf -> {
      unfold (is_tree x T.Leaf);
      fold (is_tree_cases None ft);
      rewrite is_tree_cases None ft as is_tree_cases x ft;
    }
    T.Node data ltree rtree -> {
      unfold (is_tree x (T.Node data ltree rtree));
      with p lct rct. _;
      with n. assert p |-> n;
      with l'. rewrite is_tree lct l' as is_tree n.left l';
      with r'. rewrite is_tree rct r' as is_tree n.right r';
      fold (is_tree_cases (Some p) ft);
      rewrite (is_tree_cases (Some p) ft) as is_tree_cases x ft;
    }
  }
}



 
ghost
fn is_tree_case_none (#t:Type) (x:tree_t t) (#l:T.tree t)
  requires is_tree x l
  requires pure (x == None)
  ensures is_tree x l
  ensures pure (l == T.Leaf)
{
  rewrite each x as None;
  cases_of_is_tree None l;
  unfold is_tree_cases;
  intro_is_tree_leaf x;
  ()
}



 
ghost
fn is_tree_case_some (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
  requires is_tree x ft
  requires pure (x == Some v)
ensures
   exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    (v |-> node) **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T.Node node.data ltree rtree)
  
{
  rewrite each x as Some v;
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
}


///////////////////////////////////////////////////////////////////////////////

 
fn rec height (#t:Type0) (x:tree_t t)
  requires is_tree x 'l
  returns n:nat
  ensures is_tree x 'l
  ensures pure (n == T.height 'l)
{
   match x {
    None -> {
       is_tree_case_none None;
       rewrite is_tree None 'l as is_tree x 'l;
       0
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let node = !vl;
      let l_height = height node.left;
      let r_height = height node.right;
      intro_is_tree_node x vl;
      if (l_height > r_height) {
        (l_height + 1)
      } else {
        (r_height + 1)
      }
    }
  }
}



fn is_empty (#t:Type) (x:tree_t t) (#ft:G.erased(T.tree t))
  requires is_tree x ft
  returns b:bool
  ensures is_tree x ft
  ensures pure (b <==> (T.is_empty ft))
{
  match x {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None ft as is_tree x ft;
      true
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      intro_is_tree_node x vl;
      false
    }
  }
}


let null_tree_t (t:Type0) : tree_t t = None



fn create (t:Type0)
  requires emp
  returns x:tree_t t
  ensures is_tree x T.Leaf
{
  let tree = null_tree_t t;
  intro_is_tree_leaf tree;
  tree
}


fn node_cons (#t:Type0) (v:t) (ltree:tree_t t) (rtree:tree_t t) (#l:(T.tree t)) (#r:(T.tree t)) 
  requires is_tree ltree l  **
           is_tree rtree r  //functional equivalent of x is 'l; x is the tail of the constructed tree.
  returns y:tree_t t
  ensures is_tree y (T.Node v l r)
  ensures (pure (Some? y))
{
  let y = Box.alloc { data=v; left =ltree; right = rtree };
  intro_is_tree_node (Some y) y;
  Some y
}



/// Appends value [v] at the leftmost leaf of the tree that [ptr] points to.

fn rec append_left_none (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
  requires is_tree x ft
  requires pure (None? x)
  returns y:tree_t t
  ensures is_tree x ft
  ensures is_tree y (T.Node v T.Leaf T.Leaf)
{
  let left = create t;
  let right = create t;
  let y = node_cons v left right;
  y 
}



fn rec append_left (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
  requires is_tree x ft
  returns y:tree_t t
  ensures is_tree y  (T.append_left ft v)
{
   match x {
    None -> {

      is_tree_case_none None;

      elim_is_tree_leaf None;


      let left = create t;
      let right = create t;
      
    
      let y = node_cons v left right;
      
      let np = Some?.v y;
      
      is_tree_case_some y np;

      intro_is_tree_node y np;
      y 
    }
    Some vl -> {

      is_tree_case_some (Some vl) vl;

      let node = !vl;

      let left_new = append_left node.left v;

      vl := {node with left = left_new};

      intro_is_tree_node x vl;

      x
    }
  }
} 




fn rec append_right (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
  requires is_tree x ft
  returns y:tree_t t
  ensures is_tree y  (T.append_right ft v)
{
   match x {
    None -> {

      is_tree_case_none None;

      elim_is_tree_leaf None;

      let left = create t;
      let right = create t;
      
    
      let y = node_cons v left right;
      
      let np = Some?.v y;
      
      is_tree_case_some y np;

      intro_is_tree_node y np;
      
      y 
    }
    Some np -> {
      is_tree_case_some (Some np) np;

      let node = !np;

      let right_new = append_right node.right v;
      
      np := {node with right = right_new};
      
      intro_is_tree_node x np;
      
      x
    }
  }
} 




fn node_data (#t:Type) (x:tree_t t) (#ft:G.erased (T.tree t))
    requires is_tree x ft
    requires (pure (Some? x))
    returns v:t
    ensures is_tree x ft
{
  let np = Some?.v x;
      
  is_tree_case_some x np;
      
  let node = !np;

  let v = node.data;
  
  intro_is_tree_node x np;
  v
}



fn rec mem (#t:eqtype) (x:tree_t t) (v: t) (#ft:G.erased (T.tree t))
    requires is_tree x ft
    returns b:bool
    ensures is_tree x ft
    ensures pure (b <==> (T.mem ft v))
{
  match x {
       None -> {
           is_tree_case_none None;
           rewrite is_tree None ft as is_tree x ft;
           false
       }
       Some vl -> {
           is_tree_case_some (Some vl) vl;
           let n = !vl;

           let dat = n.data;

           if (dat = v)
           {
             intro_is_tree_node x vl;
             true
           }
           else{
             let b1 = mem n.left v;
             let b2 = mem n.right v;

             let b3 = b1 || b2;
             intro_is_tree_node x vl;
             b3;

           }
       }
  }
}




fn get_some_ref (#t:Type) (x:tree_t t)
  requires is_tree x 'l
  requires pure (T.Node? 'l)
  returns v:node_ptr t
ensures  
  exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pure (x == Some v) **
    pure ('l == T.Node node.data ltree rtree) **
    (v |-> node) **
    is_tree node.left ltree **
    is_tree node.right rtree
{
  match x {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some v -> {
      is_tree_case_some (Some v) v;
      v
    }
  }
}

[@@pulse_unfold] let _left  (t:T.tree 'a{T.Node? t}) = T.Node?.left  t
[@@pulse_unfold] let _right (t:T.tree 'a{T.Node? t}) = T.Node?.right t
[@@pulse_unfold] let _data  (t:T.tree 'a{T.Node? t}) = T.Node?.data  t

fn read_node
  (#a:Type0)
  (tree : tree_t a)
  (#t : erased (T.tree a){T.Node? t})
  requires is_tree tree t
  (* ^ Some? p should be trivial, but just kick the ball to the caller *)
  returns  res : tree_t a & a & tree_t a & squash (Some? tree)
    (* ^ squash to help with spec well-formedness *)
  ensures (
    let (l, x, r, _) = res in
    (Some?.v tree |-> {left = l; data = x; right = r})
    ** is_tree l (_left t)
    ** is_tree r (_right t)
    ** pure (x == _data t)
  )
{
  let p = get_some_ref tree;
  with node. assert p |-> node;
  let n = !p;
  rewrite p |-> n as Some?.v tree |-> n;
  (n.left, n.data, n.right, ())
}

fn write_node
  (#a:Type0)
  (tree : tree_t a{Some? tree})
  (lp : tree_t a)
  (data : a)
  (rp : tree_t a)
  (#lt #rt : erased (T.tree a))
  requires
    (Some?.v tree |-> 'n0) **
    is_tree lp lt **
    is_tree rp rt
  ensures
    is_tree tree (T.Node data lt rt)
{
  let n = { data = data; left = lp; right = rp };
  let Some p = tree;
  p := n;
  fold (is_tree tree (T.Node data lt rt))
}

fn rotate_left (#t:Type0) (tree:tree_t t) (#l: G.erased (T.tree t){ Some? (T.rotate_left l) })
  requires is_tree tree l
  returns  y : tree_t t
  ensures  is_tree y (Some?.v (T.rotate_left l))
{
  let a, b, p', _  = read_node tree;
  let c, d, e,  _  = read_node p';
  write_node p' a b c;
  write_node tree p' d e;
  tree (* Note: in-place mutation, we could make this return unit instead. *)
}

fn rotate_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right l) })
  requires is_tree tree l
  returns y:tree_t t
  ensures (is_tree y (Some?.v (T.rotate_right l)))
{
  let p', d, e, _  = read_node tree;
  let a, b, c, _  = read_node p';
  write_node p' c d e;
  write_node tree a b p';
  tree
}

fn rotate_right_left (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right_left l) })
  requires is_tree tree l
  returns  y : tree_t t
  ensures  is_tree y (Some?.v (T.rotate_right_left l))
{
  let a, x, zp, _ = read_node tree;
  let yp, z, d,  _ = read_node zp;
  let b, y, c,  _ = read_node yp;
  write_node zp c z d;
  write_node yp a x b;
  write_node tree yp y zp;
  tree
}

fn rotate_left_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_left_right l) })
  requires is_tree tree l
  returns  y  :tree_t t
  ensures  is_tree y (Some?.v (T.rotate_left_right l))
{
  let zp, x, d,  _ = read_node tree;
  let a, z, yp, _ = read_node zp;
  let b, y, c,  _ = read_node yp;
  write_node zp a z b;
  write_node yp c x d;
  write_node tree zp y yp;
  tree
}


module M = FStar.Math.Lib


fn rec is_balanced (#t:Type0) (tree:tree_t t)
  requires is_tree tree 'l
  returns b:bool
  ensures is_tree tree 'l
  ensures pure (b <==> (T.is_balanced 'l))
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None 'l as is_tree tree 'l;
      true
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;

      let height_l = height n.left;
      let height_r = height n.right;

      let b1 =  (M.abs(height_r - height_l) <= 1);

      let b2 = is_balanced n.right;

      let b3 = is_balanced n.left;

      let b4 = b1 && b2 && b3;
      
      intro_is_tree_node tree vl;
      
      b4
    }
  }
}




fn rec  rebalance_avl (#t:Type0) (tree:tree_t t) (#l:G.erased(T.tree t))
  requires is_tree tree l
  returns y:tree_t t
  ensures (is_tree y (T.rebalance_avl l))
{
  let b = is_balanced tree;
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None l as is_tree tree l;
      tree
    }
    Some vl -> {
      rewrite each (Some vl) as tree;
      is_tree_case_some tree vl;
      
      if (b)
      {
        intro_is_tree_node tree vl;
        tree
      }
      else
      {
        let n = !vl;
        let height_l = height n.left;
        let height_r = height n.right;
        
        let diff_height = height_l - height_r ;

        if (diff_height > 1) 
        {
          let vll = get_some_ref n.left;
          intro_is_tree_node n.left vll;
          is_tree_case_some n.left vll;
         
          let nl = !vll;

          let height_ll = height nl.left;
          let height_lr = height nl.right;

          if (height_lr > height_ll)
          {
             (*Only in this branch, this situation happens, Node x (Node z t1 (Node y t2 t3)) t4*)
             let vllr = get_some_ref nl.right;
             
             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nl.right vllr;
             
             intro_is_tree_node n.left vll;
            
             
             intro_is_tree_node tree vl;
             
             let y = rotate_left_right tree;
             y
          }
          else
          {
            (*Node x (Node z t1 t2) t3*)
            intro_is_tree_node n.left vll;
            intro_is_tree_node tree vl;
            let y = rotate_right tree;
            y
          }
        }
        else if (diff_height < -1)
        {
          let vlr = get_some_ref n.right;
          intro_is_tree_node n.right vlr;
          is_tree_case_some n.right vlr;

          let nr = !vlr;

          let height_rl = height nr.left;
          let height_rr = height nr.right;
          if (height_rl > height_rr)
          {
             (*Node x t1 (Node z (Node y t2 t3) t4)*)
             let vlrl = get_some_ref nr.left;
             
             (*pack tree back in the order it is unpacked*)
             intro_is_tree_node nr.left vlrl;
             intro_is_tree_node n.right vlr;
             intro_is_tree_node tree vl;
             let y = rotate_right_left tree;
             y
          }
          else
          {
            (*Node x t1 (Node z t2 t3)*)
            intro_is_tree_node n.right vlr;
            intro_is_tree_node tree vl;
            let y = rotate_left tree;
            y
          }
          
        }
        else
        {
          intro_is_tree_node tree vl;
          tree
        }
        
      }
    }
  }
}



fn rec insert_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
  requires is_tree tree 'l
  returns y:tree_t t
  ensures (is_tree y (T.insert_avl cmp 'l key))
{
  match tree {
    None -> {
       is_tree_case_none None;

       elim_is_tree_leaf None;

       let left = create t;
       let right = create t;
      
    
       let y = node_cons key left right;
      
       let np = Some?.v y;
      
       is_tree_case_some y np;

       intro_is_tree_node y np;
       
       y
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      with node. assert vl |-> node;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta >= 0)
      {
        let new_left = insert_avl cmp n.left key;
        let vl' = {data = n.data; left = new_left; right = n.right};
        vl := vl';
        rewrite each new_left as vl'.left;
        rewrite each node.right as vl'.right;
        intro_is_tree_node (Some vl) vl #vl';
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
      else
      {
        let new_right = insert_avl cmp n.right key;
        let vl' = {data = n.data; left = n.left; right = new_right };
        vl := vl';
        rewrite each new_right as vl'.right;
        rewrite each node.left as vl'.left;
        intro_is_tree_node (Some vl) vl #vl';
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
    }
  }
}

 
ghost
fn is_tree_case_some1 (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
  requires is_tree x ft
  requires pure (x == Some v)
  ensures is_tree x ft
  ensures pure (T.Node? ft)
{
  rewrite each x as Some v;
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
  intro_is_tree_node (Some v) v;
  with 't. rewrite is_tree (Some v) 't as is_tree x 't;
}

fn rec tree_max_c (#t:Type0) (tree:tree_t t) (#l:G.erased(T.tree t){T.Node? l})
  requires is_tree tree l
  returns y:t
  ensures is_tree tree l
  ensures pure (y == T.tree_max l)
{
  match tree {
    None -> {
      is_tree_case_none None;
      unreachable ()
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      let n = !vl;
      match n.right {
        None -> {
          let d = n.data;
          is_tree_case_none n.right;
          intro_is_tree_node tree vl;
          d
        }
        Some vlr -> {
          is_tree_case_some1 n.right vlr;
          let max = tree_max_c n.right;
          intro_is_tree_node tree vl;
          max
        }
      }
      
    }
  }
}

fn rec delete_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
  requires is_tree tree 'l
  returns  y : tree_t t
  ensures  is_tree y (T.delete_avl cmp 'l key)
{
  match tree {
    None -> {
      is_tree_case_none None;
      rewrite is_tree None 'l as is_tree tree 'l;
      tree
    }
    Some vl -> {
      is_tree_case_some (Some vl) vl;
      with node. assert vl |-> node;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta = 0) {
        let left = n.left;
        let right = n.right;
        rewrite each node.left as left;
        rewrite each node.right as right;
        //explicit ltree and rtree is needed, to find a proof for the existence of func ltree and rtree
        with ltree. assert is_tree left ltree;
        with rtree. assert is_tree right rtree;
        match left {
          None -> {(*Leaf, _*)
            is_tree_case_none None;
            match right {
              None -> { (*Leaf,Leaf*)
                 is_tree_case_none None #rtree;
                 let tr = create t;
                 Box.free vl;
                 rewrite each rtree as T.Leaf #t;
                 rewrite each ltree as T.Leaf #t;
                 unfold is_tree #t None T.Leaf;
                 unfold is_tree #t None T.Leaf;
                 tr
              }
              Some vlr -> {(*Leaf,Node_*)
                is_tree_case_some (Some vlr) vlr;
                let rnode = !vlr;
                let vl' = {data = rnode.data; left = rnode.left; right = rnode.right};
                vl := vl';
                with ltree.
                  rewrite is_tree rnode.left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree rnode.right rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                with ltree.
                  assert (is_tree #t None ltree);
                Box.free vlr;
                elim_is_tree_leaf #t None;
                (Some vl)
              }
            }
          }
          Some vll -> {(*Node_,_*)
            is_tree_case_some1 (Some vll) vll;
            match right {
              None -> {(*Node_,Leaf*)
                is_tree_case_some (Some vll) vll;
                is_tree_case_none None;
                let lnode = !vll;
                let vl' = {data = lnode.data; left = lnode.left; right = lnode.right};
                vl := vl';
                with ltree.
                  rewrite is_tree lnode.left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree lnode.right rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                Box.free vll;
               //  rewrite (is_tree right rtree) as (is_tree right T.Leaf);
                elim_is_tree_leaf None;
                (Some vl)
              }
              Some vlr -> {(*Node_,Node_*)
                is_tree_case_some1 (Some vlr) vlr;
                let m = tree_max_c (Some vll);
                let new_left = delete_avl cmp (Some vll) m;
                let vl' = {data = m; left = new_left; right = right};
                vl := vl';
                with ltree.
                  rewrite is_tree new_left ltree as is_tree vl'.left ltree;
                with rtree.
                  rewrite is_tree (Some vlr) rtree as is_tree vl'.right rtree;
                intro_is_tree_node (Some vl) vl #vl';
                let new_tree = rebalance_avl (Some vl);
                assert (is_tree new_tree (T.delete_avl cmp 'l key));
                new_tree
              }
            }
          }
        }
      } else {
        if (delta < 0) {
          assert (pure (delta < 0));
          let new_left = delete_avl cmp n.left key;
          let vl' = {data = n.data; left = new_left; right = n.right};
          vl := vl';
          with ltree.
            rewrite is_tree new_left ltree as is_tree vl'.left ltree;
          with rtree.
            rewrite is_tree n.right rtree as is_tree vl'.right rtree;
          intro_is_tree_node (Some vl) vl #vl';
          let new_tree = rebalance_avl (Some vl);
          new_tree
        } else {
          let new_right = delete_avl cmp n.right key;
          let vl' = {data = n.data; left = n.left; right = new_right};
          vl := vl';
          with ltree.
            rewrite is_tree n.left ltree as is_tree vl'.left ltree;
          with rtree.
            rewrite is_tree new_right rtree as is_tree vl'.right rtree;
          intro_is_tree_node (Some vl) vl #vl';
  
          let new_tree = rebalance_avl (Some vl);
          assert (is_tree new_tree (T.delete_avl cmp 'l key));
          
          new_tree
        }
      }
    }
  }
}
