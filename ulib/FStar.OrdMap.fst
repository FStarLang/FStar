module FStar.OrdMap

open FStar.OrdSet
open FStar.FunctionalExtensionality

(* TODO (KM) : move me this should go in a common file on relations *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

let cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

abstract let map_t (k:eqtype) (v:Type) (f:cmp k) (d:ordset k f) =
  g:(k -> Tot (option v)){forall x. mem x d == Some? (g x)}

abstract noeq type ordmap (k:eqtype) (v:Type) (f:cmp k) =
  | Mk_map: d:ordset k f -> m:map_t k v f d -> ordmap k v f

abstract val empty   : #key:eqtype -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
abstract val const_on: #key:eqtype -> #value:Type -> #f:cmp key -> d:ordset key f -> x:value -> Tot (ordmap key value f)
abstract val select  : #key:eqtype -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
abstract val update  : #key:eqtype -> #value:Type -> #f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
abstract val contains: #key:eqtype -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
abstract val dom     : #key:eqtype -> #value:Type -> #f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)

abstract val remove  : #key:eqtype -> #value:Type -> #f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
abstract val choose  : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot (option (key * value))

abstract val size    : #key:eqtype -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot nat

let empty (#k:eqtype) (#v:Type) #f =
  let d = OrdSet.empty in
  let g = (fun x -> None) in
  Mk_map d g

let const_on (#k:eqtype) (#v:Type) #f d x =
  let g : k -> Tot (option v) = (fun y -> if mem y d then Some x else None) in
  Mk_map d g

let select (#k:eqtype) (#v:Type) #f x m = (Mk_map?.m m) x

let insert (#a:eqtype) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

let update (#k:eqtype) (#v:Type) #f x y m =
  let s' = insert x (Mk_map?.d m) in
  let g' : k -> Tot (option v) = fun (x':k) -> if x' = x then Some y else (Mk_map?.m m) x' in
  Mk_map s' g'

let contains (#k:eqtype) (#v:Type) #f x m = mem x (Mk_map?.d m)

let dom (#k:eqtype) (#v:Type) #f m = (Mk_map?.d m)

let remove (#k:eqtype) (#v:Type) #f x m =
  let s' = remove x (Mk_map?.d m) in
  let g' : k -> Tot (option v) = fun x' -> if x' = x then None else (Mk_map?.m m) x' in
  Mk_map s' g'

let choose (#k:eqtype) (#v:Type) #f m =
  match OrdSet.choose (Mk_map?.d m) with
    | None   -> None
    | Some x -> Some (x, Some?.v ((Mk_map?.m m) x))

let size (#k:eqtype) (#v:Type) #f m = OrdSet.size (Mk_map?.d m)

abstract type equal (#k:eqtype) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) =
  (forall x. select #k #v #f x m1 == select #k #v #f x m2)


abstract val eq_intro: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 == select #k #v #f x m2))
                      (ensures (equal m1 m2))
                 [SMTPat (equal m1 m2)]
  
abstract val eq_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (equal m1 m2))
                      (ensures (m1 == m2))
                 [SMTPat (equal m1 m2)]

abstract val upd_order: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                       (ensures (equal (update #k #v #f x y (update #k #v #f x' y' m))
                                       (update #k #v #f x' y' (update #k #v #f x y m))))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
                  
abstract val upd_same_k: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                        (ensures (equal (update #k #v #f x y (update #k #v #f x y' m))
					(update #k #v #f x y m)))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates

abstract val sel_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (update #k #v #f x y m) == Some y)
                 [SMTPat (select #k #v #f x (update #k #v #f x y m))]

abstract val sel_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
              -> Lemma (requires True)
                       (ensures (x =!= x' ==> (select #k #v #f x' (update #k #v #f x y m)
                                               == select #k #v #f x' m)))
                 [SMTPat (select #k #v #f x' (update #k #v #f x y m))]

abstract val sel_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
               -> Lemma (requires True)
                        (ensures (select #k #v #f x (empty #k #v #f) == None))
                  [SMTPat (select #k #v #f x (empty #k #v #f))]
                  
abstract val sel_contains: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
                  -> Lemma (requires (True))
                           (ensures (contains #k #v #f x m = Some? (select #k #v #f x m)))
                     [SMTPat (select #k #v #f x m); SMTPat (contains #k #v #f x m)]

abstract val contains_upd1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (contains #k #v #f x' (update #k #v #f x y m) =
                                      (x = x' || contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

abstract val contains_upd2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (x =!= x' ==> (contains #k #v #f x' (update #k #v #f x y m)
                                                    = contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]

abstract val contains_empty: #k:eqtype -> #v:Type -> #f:cmp k -> x:k
                    -> Lemma (requires True)
                             (ensures (not (contains #k #v #f x (empty #k #v #f))))
                       [SMTPat (contains #k #v #f x (empty #k #v #f))]

abstract val contains_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:k -> m:ordmap k v f
                     -> Lemma (requires True)
                              (ensures (contains #k #v #f x (remove #k #v #f y m) =
                                       (contains #k #v #f x m && not (x = y))))
                        [SMTPat (contains #k #v #f x (remove #k #v #f y m))]
                  
abstract val eq_remove: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires (not (contains #k #v #f x m)))
                      (ensures (equal m (remove #k #v #f x m)))
                 [SMTPat (remove #k #v #f x m)]

abstract val choose_empty: #k:eqtype -> #v:Type -> #f:cmp k
                 -> Lemma (requires True) (ensures (None? (choose #k #v #f
                                                             (empty #k #v #f))))
                    [SMTPat (choose #k #v #f (empty #k #v #f))]

abstract val choose_m: #k:eqtype -> #v:Type -> #f:cmp k -> m:ordmap k v f
             -> Lemma (requires (~ (equal m (empty #k #v #f))))
                     (ensures (Some? (choose #k #v #f m) /\
                                (select #k #v #f (fst (Some?.v (choose #k #v #f m))) m ==
                                 Some (snd (Some?.v (choose #k #v #f m)))) /\
                                (equal m (update #k #v #f (fst (Some?.v (choose #k #v #f m)))
                                                     (snd (Some?.v (choose #k #v #f m)))
                                                     (remove #k #v #f (fst (Some?.v (choose #k #v #f m))) m)))))
                [SMTPat (choose #k #v #f m)]

abstract val size_empty: #k:eqtype -> #v:Type -> #f:cmp k
                -> Lemma (requires True)
                         (ensures (size #k #v #f (empty #k #v #f) = 0))
                   [SMTPat (size #k #v #f (empty #k #v #f))]
                   
abstract val size_remove: #k:eqtype -> #v:Type -> #f:cmp k -> y:k -> m:ordmap k v f
                -> Lemma (requires (contains #k #v #f y m))
                         (ensures (size #k #v #f m = size #k #v #f (remove #k #v #f y m) + 1))
                   [SMTPat (size #k #v #f (remove #k #v #f y m))]

abstract val dom_lemma: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
               -> Lemma (requires True)
                        (ensures (contains #k #v #f x m <==>
                                  OrdSet.mem #k #f x (dom #k #v #f m)))
                  [SMTPat (mem #k #f x (dom #k #v #f m))]

abstract val contains_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                  -> Lemma (requires (True))
                           (ensures (mem y d = contains y (const_on d x)))
                                    //(contains y (const_on d x) ==> Some?.v (select p w) = x)))
                     [SMTPat (contains #k #v #f y (const_on #k #v #f d x))]
                     
abstract val select_const_on: #k:eqtype -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                     -> Lemma (requires True)
                             (ensures (mem y d ==> (contains y (const_on d x) /\ Some?.v (select y (const_on d x)) == x)))
                    [SMTPat (select #k #v #f y (const_on #k #v #f d x))]

abstract val sel_rem1: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (remove #k #v #f x m) == None)
                 [SMTPat (select #k #v #f x (remove #k #v #f x m))]

abstract val sel_rem2: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> x':k -> m:ordmap k v f
              -> Lemma (requires True) (ensures (x =!= x' ==>
                                                 select #k #v #f x'
                                                 (remove #k #v #f x m) == select #k #v #f x' m))
                 [SMTPat (select #k #v #f x' (remove #k #v #f x m))]

abstract val rem_upd: #k:eqtype -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
             -> Lemma (requires (True)) (ensures (x =!= x' ==>
                                                  equal (update #k #v #f x y (remove #k #v #f x' m))
                                                        (remove #k #v #f x' (update #k #v #f x y m))))
                [SMTPat (update #k #v #f x y (remove #k #v #f x' m))]

let eq_intro (#k:eqtype) (#v:Type) #f m1 m2 = ()

let eq_lemma (#k:eqtype) (#v:Type) #f m1 m2 =
  let Mk_map s1 g1 = m1 in
  let Mk_map s2 g2 = m2 in
  let _ = cut (feq g1 g2) in
  let _ = OrdSet.eq_lemma s1 s2 in
  assume (g1 == g2)

let upd_order (#k:eqtype) (#v:Type) #f x y x' y' m =
  let (Mk_map s1 g1) = update #k #v #f x' y' (update #k #v #f x y m) in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x' y' m) in
  cut (feq g1 g2)

let upd_same_k (#k:eqtype) (#v:Type) #f x y y' m =
  let (Mk_map s1 g1) = update #k #v #f x y m in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x y' m) in
  cut (feq g1 g2)

let sel_upd1 (#k:eqtype) (#v:Type) #f x y m = ()

let sel_upd2 (#k:eqtype) (#v:Type) #f x y x' m = ()

let sel_empty (#k:eqtype) (#v:Type) #f x = ()

let sel_contains (#k:eqtype) (#v:Type) #f x m = ()

let contains_upd1 (#k:eqtype) (#v:Type) #f x y x' m = ()

let contains_upd2 (#k:eqtype) (#v:Type) #f x y x' m = ()

let contains_empty (#k:eqtype) (#v:Type) #f x = ()

let contains_remove (#k:eqtype) (#v:Type) #f x y m = ()

let eq_remove (#k:eqtype) (#v:Type) #f x m =
  let (Mk_map s g) = m in
  let m' = remove #k #v #f x m in
  let (Mk_map s' g') = m' in
  let _ = cut (feq g g') in
  ()

let choose_empty (#k:eqtype) (#v:Type) #f = ()

private val dom_empty_helper: #k:eqtype -> #v:Type -> #f:cmp k -> m:ordmap k v f
                      -> Lemma (requires (True))
                               (ensures  ((dom #k #v #f m = OrdSet.empty) ==>
                                          (m == empty #k #v #f)))
let dom_empty_helper (#k:eqtype) (#v:Type) #f m =
  let (Mk_map s g) = m in
  if (not (s = OrdSet.empty)) then ()
  else
    let (Mk_map s' g') = empty #k #v #f in
    cut (feq g g'); assume (g == g')

let choose_m (#k:eqtype) (#v:Type) #f m =
  dom_empty_helper #k #v #f m;
  let c = choose #k #v #f m in
  match c with
    | None        -> ()
    | Some (x, y) ->
      let m' = remove #k #v #f x m in
      let (Mk_map s' g') = m' in
      let (Mk_map s'' g'') = update #k #v #f x y m' in
      cut (feq (Mk_map?.m m) g'')

let size_empty (#k:eqtype) (#v:Type) #f = ()

let size_remove (#k:eqtype) (#v:Type) #f y m = ()

let dom_lemma (#k:eqtype) (#v:Type) #f x m = ()

let contains_const_on (#k:eqtype) (#v:Type) #f d x y = ()

let select_const_on (#k:eqtype) (#v:Type) #f d x y = ()

let sel_rem1 (#k:eqtype) (#v:Type) #f x m = ()

let sel_rem2 (#k:eqtype) (#v:Type) #f x x' m = ()

let rem_upd (#k:eqtype) (#v:Type) #f x y x' m = ()
