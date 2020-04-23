module Steel.PCM.Monotonic

open FStar.Preorder
open Steel.PCM

#set-options "--fuel 0 --ifuel 1"

noeq type with_preorder
  (#a: Type u#a)
  (pcm: pcm a)
  (pre: preorder a)
  =
  | MkWithPreorder:
    fact: (fact:predicate a{stable fact pre}) ->
    value: (value:a{fact value}) ->
    with_preorder pcm pre


let composable_with_preorder'
  (#a: Type u#a)
  (#pcm: pcm a)
  (#pre: preorder a)
  (x y: with_preorder pcm pre) : prop =
  composable pcm x.value y.value /\ begin
    let value = op pcm x.value y.value in
    x.fact value /\ y.fact value
  end

let composable_with_preorder
  (#a: Type u#a)
  (#pcm: pcm a)
  (#pre: preorder a)
  : symrel (with_preorder pcm pre) =
  let composable_with_preorder =
    fun (x y: with_preorder pcm pre) -> composable_with_preorder' x y
  in
  assume(forall (x y: with_preorder pcm pre).
    composable_with_preorder x y<==> composable_with_preorder y x
  );
  composable_with_preorder


let compose_with_preorder
  (#a: Type u#a)
  (#pcm: pcm a)
  (#pre: preorder a)
  (x: with_preorder pcm pre)
  (y: with_preorder pcm pre{x `composable_with_preorder #a #pcm #pre` y})
  : with_preorder pcm pre
  =
  let value = op pcm x.value y.value in
  let fact = fun z ->
    x.fact z /\ y.fact z
  in
  MkWithPreorder #a #pcm #pre fact value

let with_preorder_pcm'
  (#a: Type u#a)
  (pcm: pcm a)
  (pre: preorder a)
    : pcm' (with_preorder pcm pre)
  = {
    composable = composable_with_preorder;
    op = compose_with_preorder;
    one = MkWithPreorder (fun _ -> True) pcm.p.one;
  }

let with_preorder_pcm
  (#a: Type u#a)
  (p: pcm a)
  (pre: preorder a)
    : pcm (with_preorder p pre)
  =
  {
    p = with_preorder_pcm' p pre;
    comm = (fun _ _ -> admit());
    assoc = (fun _ _ _ -> admit());
    assoc_r = (fun _ _ _ -> admit());
    is_unit = (fun _ -> admit())
  }
