open Prims
type 'Aa set = 'Aa -> Prims.bool
type ('Aa,'As1,'As2) equal = Prims.unit
let mem x s = s x
let empty x = false
let singleton x y = y = x
let union s1 s2 x = (s1 x) || (s2 x)
let intersect s1 s2 x = (s1 x) && (s2 x)
let complement s x = Prims.op_Negation (s x)
type ('Aa,'As1,'As2) disjoint = Prims.unit
type ('Aa,'As1,'As2) subset = Prims.unit
let mem_empty x = ()
let mem_singleton x y = ()
let mem_union x s1 s2 = ()
let mem_intersect x s1 s2 = ()
let mem_complement x s = ()
let subset_mem s1 s2 = ()
let mem_subset s1 s2 = ()
let lemma_equal_intro s1 s2 = ()
let lemma_equal_elim s1 s2 = ()
let lemma_equal_refl s1 s2 = ()
let disjoint_not_in_both s1 s2 = ()
type eqtype = Obj.t
let rec as_set' l =
  match l with | [] -> empty | hd::tl -> union (singleton hd) (as_set' tl)
let as_set l =
  match l with | [] -> empty | hd::tl -> union (singleton hd) (as_set' tl)