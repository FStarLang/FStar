(*--build-config
    options:--admit_fsi OrdSet;
    other-files:ext.fst list.fst ordset.fsi ordmap.fsi
 --*)
module OrdMap

open OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

type map_t (k:Type) (v:Type) (f:cmp k) (d:ordset k f) =
  g:(k -> Tot (option v)){(forall x. (mem f x d = is_Some (g x)))}
  
type ordmap (k:Type) (v:Type) (f:cmp k) = (dom:(ordset k f) & (map_t k v f dom))

let empty (#k:Type) (#v:Type) f =
  let d = OrdSet.empty #k f in
  let g = (fun x -> None) in
  (| d, g |)

let contains f k (| s, g |) = mem f k s

let select f k (| s, g |) = g k

let update f k v (| s, g |) =
  let s' = insert f k s in
  let g' = fun x -> if x = k then Some v else g x in
  (| s', g' |)

let dom f (| s, g |) = s

let remove f k (| s, g |) =
  let s' = remove f k s in
  let g' = fun x -> if x = k then None else g x in
  (| s', g' |)

let choose f (| s, g |) =
  match OrdSet.choose f s with
    | None   -> None
    | Some k -> Some (k, Some.v (g k))

open FunctionalExtensionality

let eq_lemma f m1 m2 =
  let (| s1, g1 |) = m1 in
  let (| s2, g2 |) = m2 in
  let _ = cut (FEq g1 g2) in
  let _ = OrdSet.eq_lemma f s1 s2 in
  ()

let empty_lem f = ()

let contains_lem f m = ()

let select_lem f k m = ()

let update_lem f k v m = ()

let remove_lem f k m = ()

val dom_empty_helper: #key:Type -> #value:Type -> f:cmp key
                      -> m:ordmap key value f
                      -> Lemma (requires (True))
                               (ensures  ((dom f m = OrdSet.empty f) ==> (m = empty f)))
let dom_empty_helper f m =
  let (| s, g |) = m in
  if (not (s = OrdSet.empty f)) then ()
  else
    let (| s', g' |) = empty f in
    let _ = cut (FEq g g') in
    let _ = OrdSet.eq_lemma f s s' in
    ()

let dom_empty f m = dom_empty_helper f m

let choose_lem f m =
  let c = choose f m in
  let (| s, g |) = m in
  match c with
    | None        -> ()
    | Some (k, v) ->
      let m' = remove f k m in
      let (| s', g' |) = m' in
      let (| s'', g'' |) = update f k v m' in
      let _ = OrdSet.eq_lemma f s s'' in
      let _ = cut (FEq g g'') in
      ()



