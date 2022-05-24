module Russell
open UnsoundUniverseLowering

//SNIPPET_START: set$
noeq
type _set : Type u#1 =
  | Set : x:Type0 -> f:(x -> set) -> _set
and set : Type0 = lower _set
//SNIPPET_END: set$

//SNIPPET_START: zero,one,two$
let zero : set = inject (Set False (fun _ -> false_elim()))
let one : set = inject (Set True (fun _ -> zero))
let two : set = inject (Set bool (fun b -> if b then zero else one))
//SNIPPET_END: zero,one,two$

//SNIPPET_START: mem$
let mem (a:set) (b:set) : Type0 =
  (v:(project b).x & (a == (project b).f v))

let not_mem (a:set) (b:set) : Type0 = mem a b -> False
//SNIPPET_END: mem$  

//SNIPPET_START: delta$
let delta_big = Set (s:set & not_mem s s) dfst
let delta : set = inject delta_big
//SNIPPET_END: delta$

//SNIPPET_START: proof$
let x_in_delta_x_not_in_delta (x:set) (mem_x_delta:mem x delta)
  : not_mem x x 
  = let (| v, r |) = mem_x_delta in // mem proofs are pairs
    let v : (project delta).x = v in // whose first component is an element of delta's indexing set
    let r : (x == (project delta).f v) = r in //and whose second component proves that x is equal to an element in delta
    inj_proj delta_big; // we use the unsound axiom to conclude that `v` is actually the indexing set of delta_big
    let v : (s:set & not_mem s s) = v in //and now we can retype `v` this way
    let r : (x == dfst v) = r in //and `r` this way
    let (| _, pf |) = v in //and now the second element of v
    let pf : not_mem x x = pf in //has the type we need
    pf

let delta_not_in_delta
  : not_mem delta delta
  = fun (mem_delta_delta:mem delta delta) ->
      x_in_delta_x_not_in_delta delta mem_delta_delta mem_delta_delta

let x_not_mem_x_x_mem_delta (x:set) (x_not_mem_x:x `not_mem` x)
  : x `mem` delta
  = let v : (s:set & not_mem s s) = (| x, x_not_mem_x |) in //an element of the indexing set of delta_big
    inj_proj delta_big; // the unsound axiom now lets us relate it to delta
    let s : (x == (project delta).f v) = //and prove that projecting delta's comprehension and applying to v return x`
        FStar.Squash.return_squash Refl
    in
    (| v,  s |)

let delta_in_delta
  : mem delta delta
  = x_not_mem_x_x_mem_delta delta delta_not_in_delta
  
let ff : False = delta_not_in_delta delta_in_delta
//SNIPPET_END: proof$
