module Steel.PCM.Monotonic

open FStar.Preorder
open Steel.PCM

#set-options "--fuel 0 --ifuel 1"

noeq type with_preorder
  (#a: Type u#a)
  (pcm: pcm a)
  =
  | MkWithPreorder:
    value: a ->
    pre: preorder a ->
    fact: (fact:predicate a{
      stable fact pre /\
      fact value
    }) ->
    with_preorder pcm

let composable_with_preorder'
  (#a: Type u#a)
  (#pcm: pcm a)
  (x y: with_preorder pcm) : prop =
  x.pre == y.pre /\
  composable pcm x.value y.value /\
  begin
    let z = op pcm x.value y.value in
    x.pre x.value z /\ x.pre y.value z /\
    ((x.fact x.value \/ y.fact y.value) ==> (x.fact z /\ y.fact z))
  end

let composable_with_preorder
  (#a: Type u#a)
  (#pcm: pcm a)
  : symrel (with_preorder pcm) =
  let composable_with_preorder =
    fun (x y: with_preorder pcm) -> composable_with_preorder' x y
  in
  assume(forall (x y: with_preorder pcm).
    composable_with_preorder x y <==> composable_with_preorder y x
  );
  composable_with_preorder


let compose_with_preorder
  (#a: Type u#a)
  (#pcm: pcm a)
  (x: with_preorder pcm)
  (y: with_preorder pcm{x `composable_with_preorder` y})
  : with_preorder pcm
  =
  let z = op pcm x.value y.value in
  MkWithPreorder z x.pre (fun z -> x.fact z /\ y.fact z)

let with_preorder_pcm'
  (#a: Type u#a)
  (pcm: pcm a)
    : pcm' (with_preorder pcm)
  = {
    composable = composable_with_preorder;
    op = compose_with_preorder;
    one = MkWithPreorder pcm.p.one (fun _ _ -> True) (fun _ -> True);
  }

let with_preorder_pcm
  (#a: Type u#a)
  (p: pcm a)
    : pcm (with_preorder p)
  =
  {
    p = with_preorder_pcm' p;
    comm = (fun _ _ -> admit());
    assoc = (fun _ _ _ -> admit());
    assoc_r = (fun _ _ _ -> admit());
    is_unit = (fun _ -> admit())
  }

open Steel.PCM.FractionalPermission

let monotonic_increase_preorder : preorder (with_perm int) =
   let rel = fun (x y: with_perm int) ->
     (readable x.perm ==> ((readable y.perm /\ x.value <= y.value) \/ not (readable x.perm))) /\
     (not (readable x.perm) ==> not (readable y.perm))
   in
   assume(transitive rel);
   rel

let monotonic_value (a: Type) (def: a) : Type = with_preorder (frac_perm_pcm def)

let monotonic_value_pcm (a: Type) (def: a) : pcm (monotonic_value a def)
  =
  with_preorder_pcm #(with_perm a) (frac_perm_pcm def)

open Steel.PCM.Memory

let monotonic_int = monotonic_value int 0

let monotonic_int_pcm = monotonic_value_pcm int 0

let monotonic_int_ref = ref monotonic_int monotonic_int_pcm

let increasing_value (v: int) (perm: perm) : monotonic_int =
  MkWithPreorder ({value = v; perm = perm}) monotonic_increase_preorder (fun _ -> True)

let increasing_value_with_fact (v: int) (perm: perm) fact : monotonic_int =
  MkWithPreorder ({value = v; perm = perm}) monotonic_increase_preorder fact


let pts_to_increasing_value (x: monotonic_int_ref) (v: int) (perm: perm) =
  pts_to x (increasing_value v perm)

let increasing_value_with_min (v: int) (perm: perm) (min: int{min <= v}) : monotonic_int =
  MkWithPreorder
    ({value = v; perm = perm})
    monotonic_increase_preorder
    (fun z -> readable z.perm ==> z.value >= min)

let witness_min
  (x: monotonic_int_ref)
  (v: int)
  (min: int{min <= v})
  : action
    (pts_to x (increasing_value v perm_one))
    unit
    (fun _ -> pts_to x (increasing_value_with_min v perm_one min))
  =
  let old_v = increasing_value v perm_one in
  let new_v = increasing_value_with_min v perm_one min in
  upd_action x old_v new_v

[@expect_failure]
let witness_min_any_perm
  (x: monotonic_int_ref)
  (v: int)
  (min: int{min <= v})
  (perm: perm)
  : action
    (pts_to x (increasing_value v perm))
    unit
    (fun _ -> pts_to x (increasing_value_with_min v perm min))
  =
  let old_v = increasing_value v perm_one in
  let new_v = increasing_value_with_min v perm_one min in
  upd_action x old_v new_v

let update_monotonic_int
   (x: monotonic_int_ref)
   (v: int)
   (new_v: int{
     monotonic_increase_preorder
       ({value = v; perm = perm_one})
       ({value = new_v; perm = perm_one})
   })
   (fact: (fact:predicate (with_perm int){
      stable fact monotonic_increase_preorder /\
      fact ({value = v; perm = perm_one})
    }))
   : action
   (pts_to x (increasing_value_with_fact v perm_one fact))
   unit
   (fun _ -> pts_to x (increasing_value_with_fact new_v perm_one fact))
   =
   let old_v = increasing_value_with_fact v perm_one fact in
   let new_v = increasing_value_with_fact new_v perm_one fact in
   upd_action x old_v new_v
