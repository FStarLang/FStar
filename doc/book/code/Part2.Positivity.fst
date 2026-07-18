module Part2.Positivity

[@@expect_failure]
//SNIPPET_START: dyn$
noeq
type dyn =
  | Bool : bool -> dyn
  | Int  : int -> dyn
  | Function : (dyn -> dyn) -> dyn
//SNIPPET_END: dyn$

//SNIPPET_START: nopos_dyn$
#push-options "--__no_positivity"
noeq
type dyn =
  | Bool : bool -> dyn
  | Int  : int -> dyn
  | Function : (dyn -> dyn) -> dyn
#pop-options
//SNIPPET_END: nopos_dyn$

//SNIPPET_START: nopos_dyn_loop$
let loop' (f:dyn)
  : dyn
  = match f with
    | Function g -> g f
    | _ -> f

let loop
  : dyn
  = loop' (Function loop')
//SNIPPET_END: nopos_dyn_loop$

//SNIPPET_START: non_positive$
#push-options "--__no_positivity"
noeq
type non_positive =
  | NP : (non_positive -> False) -> non_positive
#pop-options

let almost_false (f:non_positive)
  : False
  = let NP g = f in g f

let ff
  : False
  = almost_false (NP almost_false)
//SNIPPET_END: non_positive$

//SNIPPET_START: also_non_positive$
#push-options "--__no_positivity"
noeq
type also_non_pos (f:Type -> Type) =
  | ANP : f (also_non_pos f) -> also_non_pos f
#pop-options

let f_false
  : Type -> Type
  = fun a -> (a -> False)

let almost_false_again
  : f_false (also_non_pos f_false)
  = fun x -> let ANP h = x in h x

let ff_again
  : False
  = almost_false_again (ANP almost_false_again)
//SNIPPET_END: also_non_positive$


//SNIPPET_START: free$
noeq
type free (f:([@@@ strictly_positive] _:Type -> Type))
          (a:Type) 
  : Type =
  | Leaf : a -> free f a
  | Branch : f (free f a) -> free f a
//SNIPPET_END: free$

//SNIPPET_START: free_instances$
let binary_tree (a:Type) = free (fun t -> t & t) a
let list_redef ([@@@strictly_positive] a:Type) = list a
let variable_branching_list a = free list_redef a
let infinite_branching_tree a = free (fun t -> nat -> t) a
//SNIPPET_END: free_instances$

[@@expect_failure]
//SNIPPET_START: free_bad$
let free_bad = free (fun t -> (t -> False)) int
//SNIPPET_END: free_bad$

//SNIPPET_START: unused$
irreducible
let ref ([@@@unused] a:Type) = nat
noeq
type linked_list (a:Type) =
  | LL : ref (a & linked_list a) -> linked_list a
noeq
type neg_unused =
  | NU : ref (neg_unused -> bool) -> neg_unused
//SNIPPET_END: unused$
