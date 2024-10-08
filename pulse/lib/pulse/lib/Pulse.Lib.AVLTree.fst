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

noeq
type node (t:Type0) = {
    data : t;
    left : tree_t t;
    right : tree_t t;
}

and node_ptr (t:Type0) = ref (node t)

//A nullable pointer to a node
and tree_t (t:Type0) = option (node_ptr t)

let rec is_tree #t ct ft = match ft with
  | T.Leaf -> pure (ct == None)
  | T.Node data left' right' ->
    exists* (p:node_ptr t) (lct:tree_t t) (rct:tree_t t).
      pure (ct == Some p) **
      pts_to p { data = data ; left = lct ; right = rct} **
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
    pts_to p { data; left = lct;right = rct } **
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
  pts_to v node **
  is_tree node.left ltree **
  is_tree node.right rtree **
  pure (ct == Some v)
ensures
  is_tree ct (T.Node node.data ltree rtree)
{
  fold (is_tree ct (T.Node node.data ltree rtree))
}


let is_tree_cases #t (x : option (ref (node t))) ft
= match x with
  | None -> pure (ft == T.Leaf)
  | Some v -> 
    exists* (n:node t) (ltree:T.tree t) (rtree:T.tree t).
      pts_to v n **
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
    }
    T.Node data ltree rtree -> {
      unfold (is_tree x (T.Node data ltree rtree));
      with p _lct _rct. _;
      fold (is_tree_cases (Some p) ft)
    }
  }
}



 
ghost
fn is_tree_case_none (#t:Type) (x:tree_t t) (#l:T.tree t)
requires is_tree x l ** pure (x == None)
ensures  is_tree x l ** pure (l == T.Leaf)
{
  cases_of_is_tree None l;
  unfold is_tree_cases;
  intro_is_tree_leaf x;
}



 
ghost
fn is_tree_case_some (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
requires is_tree x ft ** pure (x == Some v)
ensures  
   exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree **
    pure (ft == T.Node node.data ltree rtree)
  
{
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
}


///////////////////////////////////////////////////////////////////////////////

 
fn rec height (#t:Type0) (x:tree_t t)
requires is_tree x 'l
returns n:nat
ensures is_tree x 'l ** pure (n == T.height 'l)
{
   match x {
    None -> {
       is_tree_case_none x;
       0
    }
    Some vl -> {
      is_tree_case_some x vl;
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
  ensures is_tree x ft ** pure (b <==> (T.is_empty ft))
{
  match x {
    None -> {
      is_tree_case_none x;
      true
    }
    Some vl -> {
      is_tree_case_some x vl;
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
  ensures is_tree y (T.Node v l r) ** (pure (Some? y))
{
  let y = alloc { data=v; left =ltree; right = rtree };
  rewrite each ltree as ({data = v; left = ltree; right = rtree}).left in (is_tree ltree l);
  rewrite each rtree as ({data = v; left = ltree; right = rtree}).right in (is_tree rtree r);
  intro_is_tree_node (Some y) y;
  Some y
}



/// Appends value [v] at the leftmost leaf of the tree that [ptr] points to.

fn rec append_left_none (#t:Type0) (x:tree_t t) (v:t) (#ft:G.erased (T.tree t))
requires is_tree x ft ** pure (None? x)
returns y:tree_t t
ensures is_tree x ft  ** is_tree y (T.Node v T.Leaf T.Leaf)
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
      
      is_tree_case_none x;
      
      elim_is_tree_leaf x;
      
      
      let left = create t;
      let right = create t;
      
    
      let y = node_cons v left right;
      
      let np = Some?.v y;
      
      is_tree_case_some y np;

      intro_is_tree_node y np;
      y 
    }
    Some vl -> {
      
      let np = Some?.v x;
      
      is_tree_case_some x np;
     
      with _node _ltree _rtree._;
     
      let node = !np;
     
      rewrite each _node as node;

      let left_new = append_left node.left v;
      
      np := {node with left = left_new};
      
      rewrite each left_new as ({ node with left = left_new }).left in (is_tree left_new ((T.append_left (reveal _ltree) v)));
      
      rewrite each node.right as ({ node with left = left_new }).right in (is_tree node.right _rtree);
       
      intro_is_tree_node x np;

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
      
      is_tree_case_none x;
      
      elim_is_tree_leaf x;
     
      let left = create t;
      let right = create t;
      
    
      let y = node_cons v left right;
      
      let np = Some?.v y;
      
      is_tree_case_some y np;

      intro_is_tree_node y np;
      
      y 
    }
    Some vl -> {
      
      let np = Some?.v x;
      
      is_tree_case_some x np;
      
      with _node _ltree _rtree._;
      
      let node = !np;
      
      rewrite each _node as node;

      let right_new = append_right node.right v;
      
      np := {node with right = right_new};
      
      rewrite each right_new as ({ node with right = right_new }).right in (is_tree right_new ((T.append_right (reveal _rtree) v)));
      
      rewrite each node.left as ({node with right = right_new}).left in (is_tree node.left _ltree);
      
      intro_is_tree_node x np;
      
      x
    }
  }
} 




fn node_data (#t:Type) (x:tree_t t) (#ft:G.erased (T.tree t))
    requires is_tree x ft  ** (pure (Some? x))
    returns v:t
    ensures is_tree x ft
{
  let np = Some?.v x;
      
  is_tree_case_some x np;
      
  with _node _ltree _rtree._;
      
  let node = !np;
      
  rewrite each _node as node;

  let v = node.data;
  
  intro_is_tree_node x np;
  v
}



fn rec mem (#t:eqtype) (x:tree_t t) (v: t) (#ft:G.erased (T.tree t))
    requires is_tree x ft
    returns b:bool
    ensures is_tree x ft ** pure (b <==> (T.mem ft v))
{
   match x {
        None -> {
            is_tree_case_none x;
            false
        }
        Some vl -> {
            is_tree_case_some x vl;
            with _node _ltree _rtree. _;
            let n = !vl;
            rewrite each _node as n;

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
requires is_tree x 'l ** pure (T.Node? 'l)
returns v:node_ptr t
ensures  
  exists* (node:node t) (ltree:T.tree t) (rtree:T.tree t).
    pure (x == Some v) **
    pure ('l == T.Node node.data ltree rtree) **
    pts_to v node **
    is_tree node.left ltree **
    is_tree node.right rtree
{
  match x {
    None -> {
      is_tree_case_none x;
      unreachable ()
    }
    Some v -> {
      is_tree_case_some x v;
      v
    }
  }
}



fn rotate_left (#t:Type0) (tree:tree_t t) (#l: G.erased (T.tree t){ Some? (T.rotate_left l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_left l)))
{
  let vl = get_some_ref tree;
  let n = !vl;
  let vlr = get_some_ref n.right;
  let nr = !vlr;
  
  vlr := { data = n.data; left = n.left; right = nr.left };
  
  intro_is_tree_node (Some vlr) vlr #{data = n.data; left = n.left; right = nr.left};
  
  vl := { data = nr.data; left = Some vlr; right = nr.right };
  
  intro_is_tree_node (Some vl) vl #{data = nr.data; left = Some vlr; right = nr.right};
  
  Some vl
}




fn rotate_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_right l)))
{
  let vl = get_some_ref tree;
  let n = !vl;
  let vll = get_some_ref n.left;
  let nl = !vll;

  vll := {data = n.data; left = nl.right; right = n.right};

  intro_is_tree_node (Some vll) vll #{data = n.data; left = nl.right; right = n.right};

  vl := {data = nl.data; left = nl.left; right = Some vll};

  intro_is_tree_node (Some vl) vl #{data = nl.data; left = nl.left; right = Some vll};
  Some vl
}




fn rotate_right_left (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_right_left l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_right_left l)))
{
  let vl = get_some_ref tree;
  let n = !vl;

  let vlr = get_some_ref n.right;

  let nr = !vlr;
  
  let vlrl = get_some_ref nr.left;

  let nrl = !vlrl;

  vlr := {data = nr.data; left = nrl.right; right = nr.right};
  
  intro_is_tree_node (Some vlr) vlr #{data = nr.data; left = nrl.right; right = nr.right};
  
  vlrl := {data = n.data; left = n.left; right = nrl.left};

  intro_is_tree_node (Some vlrl) vlrl #{data = n.data; left = n.left; right = nrl.left};

  vl := {data = nrl.data; left = Some vlrl; right = Some vlr};

  intro_is_tree_node (Some vl) vl #{data = nrl.data; left = Some vlrl; right = Some vlr};

  Some vl
}



fn rotate_left_right (#t:Type0) (tree:tree_t t) (#l:G.erased (T.tree t){ Some? (T.rotate_left_right l) })
requires is_tree tree l
returns y:tree_t t 
ensures (is_tree y (Some?.v (T.rotate_left_right l)))
{
  (*Node x (Node z t1 (Node y t2 t3)) t4 -> Some (Node y (Node z t1 t2) (Node x t3 t4))
                      |----vllr---|
           |----------vll-----------|
   |---------vl------------------------|            *)
  let vl = get_some_ref tree;

  let n = !vl;

  let vll = get_some_ref n.left;

  let nl = !vll;

  let vllr = get_some_ref nl.right;

  let nlr = !vllr;

  vllr := {data = n.data; left = nlr.right; right = n.right};

  vll := {data = nl.data; left = nl.left; right = nlr.left};

  intro_is_tree_node (Some vllr) vllr #{data = n.data; left = nlr.right; right = n.right};

  intro_is_tree_node (Some vll) vll #{data = nl.data; left = nl.left; right = nlr.left};

  vl := {data = nlr.data; left = Some (vll); right = Some vllr};

  intro_is_tree_node (Some vl) vl #{data = nlr.data; left = Some (vll); right = Some vllr};
  
  Some vl
}


module M = FStar.Math.Lib


fn rec is_balanced (#t:Type0) (tree:tree_t t)
requires is_tree tree 'l
returns b:bool
ensures is_tree tree 'l ** pure (b <==> (T.is_balanced 'l))
{
  match tree {
    None -> {
      is_tree_case_none tree;
      true
    }
    Some vl -> {
      is_tree_case_some tree vl;
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
      is_tree_case_none tree;
      tree
    }
    Some vl -> {
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
       is_tree_case_none tree;
      
       elim_is_tree_leaf tree;
     
       let left = create t;
       let right = create t;
      
    
       let y = node_cons key left right;
      
       let np = Some?.v y;
      
       is_tree_case_some y np;

       intro_is_tree_node y np;
       
       y
    }
    Some vl -> {
      is_tree_case_some tree vl;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta >= 0)
      {
        let new_left = insert_avl cmp n.left key;
        vl := {data = n.data; left = new_left; right = n.right};
        intro_is_tree_node (Some vl) vl #({data = n.data; left = new_left; right = n.right});
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
      else
      {
        let new_right = insert_avl cmp n.right key;
        vl := {data = n.data; left = n.left; right = new_right};
        intro_is_tree_node (Some vl) vl #({data = n.data; left = n.left; right = new_right});
        let new_tree = rebalance_avl (Some vl);
        new_tree
      }
    }
  }
}

 
ghost
fn is_tree_case_some1 (#t:Type) (x:tree_t t) (v:node_ptr t) (#ft:T.tree t) 
requires is_tree x ft ** pure (x == Some v)
ensures  is_tree x ft ** pure (T.Node? ft)
{
  cases_of_is_tree (Some v) ft;
  unfold is_tree_cases;
  intro_is_tree_node (Some v) v;
}


#set-options "--print_full_names"


fn rec tree_max_c (#t:Type0) (tree:tree_t t) (#l:G.erased(T.tree t){T.Node? l})
requires is_tree tree l 
returns y:t 
ensures is_tree tree l ** pure (y == T.tree_max l)
{
  match tree {
    None -> {
      is_tree_case_none tree;
      unreachable ()
    }
    Some vl -> {
      is_tree_case_some tree vl;
      let n = !vl;
      let right = n.right;
      match right {
        None -> {
          let d = n.data;
          is_tree_case_none right;
          intro_is_tree_node tree vl;
          d
        }
        Some vlr -> {
          is_tree_case_some1 right vlr;
          let max = tree_max_c right;
          intro_is_tree_node tree vl;
          max
        }
      }
      
    }
  }
}



fn rec delete_avl (#t:Type0) (cmp: T.cmp t) (tree:tree_t t) (key: t)
requires is_tree tree 'l
returns y:tree_t t 
ensures (is_tree y (T.delete_avl cmp 'l key))
{
  match tree{
   None -> {
    is_tree_case_none tree;
      tree
   }
   Some vl -> {
    is_tree_case_some tree vl;
      let n = !vl;
      let delta = cmp n.data key;
      if (delta = 0){
       let left = n.left;
       let right = n.right;
       //explicit ltree and rtree is needed, to find a proof for the existence of func ltree and rtree
       with ltree. assert (is_tree left ltree);
       with rtree. assert (is_tree right rtree);
       match left {
        None -> {(*Leaf, _*)
          is_tree_case_none left;
          match right {
            None -> { (*Leaf,Leaf*)
               is_tree_case_none right #rtree;
               let tr= create t;
               free vl;
               rewrite (is_tree left ltree) as (is_tree left T.Leaf);
               elim_is_tree_leaf left;
               elim_is_tree_leaf right;
               tr
            }
            Some vlr -> {(*Leaf,Node_*)
              is_tree_case_some right vlr;
              let rnode = !vlr;
              vl := {data = rnode.data; left = rnode.left; right = rnode.right};
              intro_is_tree_node (Some vl) vl #({data = rnode.data; left = rnode.left; right = rnode.right});
              free vlr;
              rewrite (is_tree left ltree) as (is_tree left T.Leaf);
              elim_is_tree_leaf left;
              
              (Some vl)
            }
          }
        }
        Some vll -> {(*Node_,_*)
        is_tree_case_some1 left vll;
          match right {
            None -> {(*Node_,Leaf*)
              is_tree_case_some left vll;
              is_tree_case_none right;
              let lnode = !vll;
              vl := {data = lnode.data; left = lnode.left; right = lnode.right};
              intro_is_tree_node (Some vl) vl #({data = lnode.data; left = lnode.left; right = lnode.right});
              free vll;
              rewrite (is_tree right rtree) as (is_tree right T.Leaf);
              elim_is_tree_leaf right;
              (Some vl)
            }
            Some vlr -> {(*Node_,Node_*)
              is_tree_case_some1 right vlr;
              let m = tree_max_c left;
              let new_left = delete_avl cmp left m;
              vl := {data = m; left = new_left; right = right};
              intro_is_tree_node (Some vl) vl #({data = m; left = new_left; right = right});
              let new_tree = rebalance_avl (Some vl);
              assert (is_tree new_tree (T.delete_avl cmp 'l key));
              
              new_tree
            }
          }
        }
       }
      }
      else{
        if (delta < 0) {
          assert (pure (delta < 0));
          let new_left = delete_avl cmp n.left key;
          vl := {data = n.data; left = new_left; right = n.right};
          intro_is_tree_node (Some vl) vl #({data = n.data; left = new_left; right = n.right});
          let new_tree = rebalance_avl (Some vl);
          new_tree
        }
        else{
          let new_right = delete_avl cmp n.right key;
          vl := {data = n.data; left = n.left; right = new_right};
          intro_is_tree_node (Some vl) vl #({data = n.data; left = n.left; right = new_right});
          
          let new_tree = rebalance_avl (Some vl);
          assert (is_tree new_tree (T.delete_avl cmp 'l key));
          
          new_tree
        }
      }
   }
  }
}


