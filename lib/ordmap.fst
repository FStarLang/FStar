(*--build-config
    options:--admit_fsi OrdSet --admit_fsi Set --logQueries;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst list.fst ordset.fsi ordmap.fsi
 --*)
module OrdMap

open OrdSet

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

let select (#k:Type) (#v:Type) #f x (Mk_map d m) = m x

let update (#k:Type) (#v:Type) #f x y (Mk_map s g ) =
  let s' = insert x s in
  let g' = fun x' -> if x' = x then Some y else g x' in
  Mk_map s' g'

let contains (#k:Type) (#v:Type) #f x (Mk_map s g) = mem x s

let dom (#k:Type) (#v:Type) #f (Mk_map s g) = s

let remove (#k:Type) (#v:Type) #f x (Mk_map s g) =
  let s' = remove x s in
  let g' = fun x' -> if x' = x then None else g x' in
  Mk_map s' g'

let choose (#k:Type) (#v:Type) #f (Mk_map s g) =
  match OrdSet.choose s with
    | None   -> None
    | Some x -> Some (x, Some.v (g x))

let size (#k:Type) (#v:Type) #f (Mk_map s g) = OrdSet.size s

open FunctionalExtensionality

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
#reset-options
let sel_contains (#k:Type) (#v:Type) #f x m = ()

