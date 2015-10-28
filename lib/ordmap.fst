(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst ordset.fsi ordmap.fsi
 --*)
module FStar.OrdMap

open FStar.OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type map_t (k:Type) (v:Type) (f:cmp k) (d:ordset k f) =
  g:(k -> Tot (option v)){(forall x. (mem x d = is_Some (g x)))}

type ordmap: key:Type -> value:Type -> cmp key -> Type =
  | Mk_map: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> m:map_t k v f d -> ordmap k v f

let empty (#k:Type) (#v:Type) #f =
  let d = OrdSet.empty in
  let g = (fun x -> None) in
  Mk_map d g

let const_on (#k:Type) (#v:Type) #f d x =
  let g = (fun y -> if mem y d then Some x else None) in
  Mk_map d g

let select (#k:Type) (#v:Type) #f x m = (Mk_map.m m) x

let insert (#a:Type) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

let update (#k:Type) (#v:Type) #f x y m =
  let s' = insert x (Mk_map.d m) in
  let g' = fun x' -> if x' = x then Some y else (Mk_map.m m) x' in
  Mk_map s' g'

let contains (#k:Type) (#v:Type) #f x m = mem x (Mk_map.d m)

let dom (#k:Type) (#v:Type) #f m = (Mk_map.d m)

let remove (#k:Type) (#v:Type) #f x m =
  let s' = remove x (Mk_map.d m) in
  let g' = fun x' -> if x' = x then None else (Mk_map.m m) x' in
  Mk_map s' g'

let choose (#k:Type) (#v:Type) #f m =
  match OrdSet.choose (Mk_map.d m) with
    | None   -> None
    | Some x -> Some (x, Some.v ((Mk_map.m m) x))

let size (#k:Type) (#v:Type) #f m = OrdSet.size (Mk_map.d m)

open FStar.FunctionalExtensionality

opaque type Equal (#k:Type) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) = 
  (forall x. select #k #v #f x m1 = select #k #v #f x m2)

let eq_intro (#k:Type) (#v:Type) #f m1 m2 = ()

let eq_lemma (#k:Type) (#v:Type) #f m1 m2 =
  let Mk_map s1 g1 = m1 in
  let Mk_map s2 g2 = m2 in
  let _ = cut (FEq g1 g2) in
  let _ = OrdSet.eq_lemma s1 s2 in
  ()

let upd_order (#k:Type) (#v:Type) #f x y x' y' m =
  let (Mk_map s1 g1) = update #k #v #f x' y' (update #k #v #f x y m) in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x' y' m) in
  cut (FEq g1 g2)

let upd_same_k (#k:Type) (#v:Type) #f x y y' m =
  let (Mk_map s1 g1) = update #k #v #f x y m in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x y' m) in
  cut (FEq g1 g2)

let sel_upd1 (#k:Type) (#v:Type) #f x y m = ()

let sel_upd2 (#k:Type) (#v:Type) #f x y x' m = ()

let sel_empty (#k:Type) (#v:Type) #f x = ()

let sel_contains (#k:Type) (#v:Type) #f x m = ()

let contains_upd1 (#k:Type) (#v:Type) #f x y x' m = ()

let contains_upd2 (#k:Type) (#v:Type) #f x y x' m = ()

let contains_empty (#k:Type) (#v:Type) #f x = ()

let contains_remove (#k:Type) (#v:Type) #f x y m = ()

let eq_remove (#k:Type) (#v:Type) #f x m =
  let (Mk_map s g) = m in
  let m' = remove #k #v #f x m in
  let (Mk_map s' g') = m' in
  let _ = cut (FEq g g') in
  ()

let choose_empty (#k:Type) (#v:Type) #f = ()

val dom_empty_helper: #k:Type -> #v:Type -> #f:cmp k -> m:ordmap k v f
                      -> Lemma (requires (True))
                               (ensures  ((dom #k #v #f m = OrdSet.empty) ==>
                                          (m = empty #k #v #f)))
let dom_empty_helper (#k:Type) (#v:Type) #f m =
  let (Mk_map s g) = m in
  if (not (s = OrdSet.empty)) then ()
  else
    let (Mk_map s' g') = empty #k #v #f in
    cut (FEq g g')

let choose_m (#k:Type) (#v:Type) #f m =
  dom_empty_helper #k #v #f m;
  let c = choose #k #v #f m in
  match c with
    | None        -> ()
    | Some (x, y) ->
      let m' = remove #k #v #f x m in
      let (Mk_map s' g') = m' in
      let (Mk_map s'' g'') = update #k #v #f x y m' in
      cut (FEq (Mk_map.m m) g'')

let size_empty (#k:Type) (#v:Type) #f = ()

let size_remove (#k:Type) (#v:Type) #f y m = ()

let dom_lemma (#k:Type) (#v:Type) #f x m = ()

let contains_const_on (#k:Type) (#v:Type) #f d x y = ()

let select_const_on (#k:Type) (#v:Type) #f d x y = ()

let sel_rem1 (#k:Type) (#v:Type) #f x m = ()

let sel_rem2 (#k:Type) (#v:Type) #f x x' m = ()

let rem_upd (#k:Type) (#v:Type) #f x y x' m = ()
