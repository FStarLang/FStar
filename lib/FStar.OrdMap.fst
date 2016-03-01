module FStar.OrdMap
open FStar.OrdSet


opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

private type map_t (k:Type) (v:Type) (f:cmp k) (d:ordset k f) =
  g:(k -> Tot (option v)){(forall x. (mem #k #f x d = is_Some (g x)))}

abstract type ordmap: key:Type -> value:Type -> cmp key -> Type =
  | Mk_map: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> m:map_t k v f d -> ordmap k v f

abstract val empty   : #key:Type -> #value:Type -> #f:cmp key -> Tot (ordmap key value f)
let empty (#k:Type) (#v:Type) #f =
  let d = OrdSet.empty #k #f in
  let g = (fun x -> None) in
  Mk_map d g

abstract val const_on: #key:Type -> #value:Type -> #f:cmp key -> d:ordset key f -> x:value -> Tot (ordmap key value f)
let const_on (#k:Type) (#v:Type) #f d x =
  let g = (fun y -> if mem #k #f y d then Some x else None) in
  Mk_map d g

abstract val select  : #key:Type -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
let select (#k:Type) (#v:Type) #f x m = (Mk_map.m m) x

let insert (#a:Type) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

abstract val update  : #key:Type -> #value:Type -> #f:cmp key -> key -> value
              -> m:ordmap key value f -> Tot (ordmap key value f)
let update (#k:Type) (#v:Type) #f x y m =
  let s' = insert #k #f x (Mk_map.d m) in
  let g' = fun x' -> if x' = x then Some y else (Mk_map.m m) x' in
  Mk_map s' g'

abstract val contains: #key:Type -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
let contains (#k:Type) (#v:Type) #f x m = mem #k #f x (Mk_map.d m)

abstract val dom     : #key:Type -> #value:Type -> #f:cmp key -> m:ordmap key value f ->
              Tot (ordset key f)
let dom (#k:Type) (#v:Type) #f m = (Mk_map.d m)

abstract val remove  : #key:Type -> #value:Type -> #f:cmp key -> key
              -> ordmap key value f -> Tot (ordmap key value f)
let remove (#k:Type) (#v:Type) #f x m =
  let s' = remove #k #f x (Mk_map.d m) in
  let g' = fun x' -> if x' = x then None else (Mk_map.m m) x' in
  Mk_map s' g'

abstract val choose  : #key:Type -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot (option (key * value))
let choose (#k:Type) (#v:Type) #f m =
  match OrdSet.choose #k #f (Mk_map.d m) with
    | None   -> None
    | Some x -> Some (x, Some.v ((Mk_map.m m) x))

abstract val size    : #key:Type -> #value:Type -> #f:cmp key -> ordmap key value f
              -> Tot nat
let size (#k:Type) (#v:Type) #f m = OrdSet.size #k #f (Mk_map.d m)

(*********************************************************************************)
open FStar.FunctionalExtensionality

abstract opaque type Equal (#k:Type) (#v:Type) (#f:cmp k) (m1:ordmap k v f) (m2:ordmap k v f) = 
  (forall x. select #k #v #f x m1 = select #k #v #f x m2)

abstract val eq_intro: #k:Type -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (forall x. select #k #v #f x m1 = select #k #v #f x m2))
                      (ensures (Equal m1 m2))
                 [SMTPatT (Equal m1 m2)]
let eq_intro (#k:Type) (#v:Type) #f m1 m2 = ()
  
abstract val eq_lemma: #k:Type -> #v:Type -> #f:cmp k -> m1:ordmap k v f -> m2:ordmap k v f
              -> Lemma (requires (Equal m1 m2))
                      (ensures (m1 = m2))
                 [SMTPatT (Equal m1 m2)]
let eq_lemma (#k:Type) (#v:Type) #f m1 m2 =
  let Mk_map s1 g1 = m1 in
  let Mk_map s2 g2 = m2 in
  let _ = cut (FEq g1 g2) in
  let _ = OrdSet.eq_lemma #k #f s1 s2 in
  ()

abstract val upd_order: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> y':v
               -> m:ordmap k v f
               -> Lemma (requires (x =!= x'))
                       (ensures (Equal (update #k #v #f x y (update #k #v #f x' y' m))
                                       (update #k #v #f x' y' (update #k #v #f x y m))))
                  [SMTPat (update #k #v #f x y (update #k #v #f x' y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
let upd_order (#k:Type) (#v:Type) #f x y x' y' m =
  let (Mk_map s1 g1) = update #k #v #f x' y' (update #k #v #f x y m) in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x' y' m) in
  cut (FEq g1 g2)

abstract val upd_same_k: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> y':v
                -> m:ordmap k v f
                -> Lemma (requires (True))
                        (ensures (Equal (update #k #v #f x y (update #k #v #f x y' m))
					(update #k #v #f x y m)))
                   [SMTPat (update #k #v #f x y (update #k #v #f x y' m))] //NS:This pattern is too aggresive; it will fire for any pair of updates
let upd_same_k (#k:Type) (#v:Type) #f x y y' m =
  let (Mk_map s1 g1) = update #k #v #f x y m in
  let (Mk_map s2 g2) = update #k #v #f x y (update #k #v #f x y' m) in
  cut (FEq g1 g2)

abstract val sel_upd1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (update #k #v #f x y m) = Some y)
                 [SMTPat (select #k #v #f x (update #k #v #f x y m))]
let sel_upd1 (#k:Type) (#v:Type) #f x y m = ()

abstract val sel_upd2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
              -> Lemma (requires True)
                       (ensures (x =!= x' ==> (select #k #v #f x' (update #k #v #f x y m)
                                               = select #k #v #f x' m)))
                 [SMTPat (select #k #v #f x' (update #k #v #f x y m))]
let sel_upd2 (#k:Type) (#v:Type) #f x y x' m = ()

abstract val sel_empty: #k:Type -> #v:Type -> #f:cmp k -> x:k
               -> Lemma (requires True)
                        (ensures (select #k #v #f x (empty #k #v #f) = None))
                  [SMTPat (select #k #v #f x (empty #k #v #f))]
let sel_empty (#k:Type) (#v:Type) #f x = ()
                  
abstract val sel_contains: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
                  -> Lemma (requires (True))
                           (ensures (contains #k #v #f x m = is_Some (select #k #v #f x m)))
                     [SMTPat (select #k #v #f x m); SMTPat (contains #k #v #f x m)]
let sel_contains (#k:Type) (#v:Type) #f x m = ()

abstract val contains_upd1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (contains #k #v #f x' (update #k #v #f x y m) =
                                      (x = x' || contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]
let contains_upd1 (#k:Type) (#v:Type) #f x y x' m = ()

abstract val contains_upd2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k
                   -> m:ordmap k v f
                   -> Lemma (requires True)
                            (ensures (x =!= x' ==> (contains #k #v #f x' (update #k #v #f x y m)
                                                    = contains #k #v #f x' m)))
                      [SMTPat (contains #k #v #f x' (update #k #v #f x y m))]
let contains_upd2 (#k:Type) (#v:Type) #f x y x' m = ()

abstract val contains_empty: #k:Type -> #v:Type -> #f:cmp k -> x:k
                    -> Lemma (requires True)
                             (ensures (not (contains #k #v #f x (empty #k #v #f))))
                       [SMTPat (contains #k #v #f x (empty #k #v #f))]
let contains_empty (#k:Type) (#v:Type) #f x = ()

abstract val contains_remove: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:k -> m:ordmap k v f
                     -> Lemma (requires True)
                              (ensures (contains #k #v #f x (remove #k #v #f y m) =
                                       (contains #k #v #f x m && not (x = y))))
                        [SMTPat (contains #k #v #f x (remove #k #v #f y m))]
let contains_remove (#k:Type) (#v:Type) #f x y m = ()
                  
abstract val eq_remove: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires (not (contains #k #v #f x m)))
                      (ensures (Equal m (remove #k #v #f x m)))
                 [SMTPat (remove #k #v #f x m)]
let eq_remove (#k:Type) (#v:Type) #f x m =
  let (Mk_map s g) = m in
  let m' = remove #k #v #f x m in
  let (Mk_map s' g') = m' in
  let _ = cut (FEq g g') in
  ()

abstract val choose_empty: #k:Type -> #v:Type -> #f:cmp k
                 -> Lemma (requires True) (ensures (is_None (choose #k #v #f
                                                             (empty #k #v #f))))
                    [SMTPat (choose #k #v #f (empty #k #v #f))]
let choose_empty (#k:Type) (#v:Type) #f = ()

private val dom_empty_helper: #k:Type -> #v:Type -> #f:cmp k -> m:ordmap k v f
                      -> Lemma (requires (True))
                               (ensures  ((dom #k #v #f m = OrdSet.empty #k #f) ==>
                                          (m = empty #k #v #f)))
let dom_empty_helper (#k:Type) (#v:Type) #f m =
  let (Mk_map s g) = m in
  if (not (s = OrdSet.empty #k #f)) then ()
  else
    let (Mk_map s' g') = empty #k #v #f in
    cut (FEq g g')

abstract val choose_m: #k:Type -> #v:Type -> #f:cmp k -> m:ordmap k v f
             -> Lemma (requires (~ (Equal m (empty #k #v #f))))
                     (ensures (is_Some (choose #k #v #f m) /\
                                (select #k #v #f (fst (Some.v (choose #k #v #f m))) m =
                                 Some (snd (Some.v (choose #k #v #f m)))) /\
                                (Equal m (update #k #v #f (fst (Some.v (choose #k #v #f m)))
                                                     (snd (Some.v (choose #k #v #f m)))
                                                     (remove #k #v #f (fst (Some.v (choose #k #v #f m))) m)))))
                [SMTPat (choose #k #v #f m)]
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

abstract val size_empty: #k:Type -> #v:Type -> #f:cmp k
                -> Lemma (requires True)
                         (ensures (size #k #v #f (empty #k #v #f) = 0))
                   [SMTPat (size #k #v #f (empty #k #v #f))]
let size_empty (#k:Type) (#v:Type) #f = ()
                   
abstract val size_remove: #k:Type -> #v:Type -> #f:cmp k -> y:k -> m:ordmap k v f
                -> Lemma (requires (contains #k #v #f y m))
                         (ensures (size #k #v #f m = size #k #v #f (remove #k #v #f y m) + 1))
                   [SMTPat (size #k #v #f (remove #k #v #f y m))]
let size_remove (#k:Type) (#v:Type) #f y m = ()

abstract val dom_lemma: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
               -> Lemma (requires True)
                        (ensures (contains #k #v #f x m <==>
                                  OrdSet.mem #k #f x (dom #k #v #f m)))
                  [SMTPat (mem #k #f x (dom #k #v #f m))]
let dom_lemma (#k:Type) (#v:Type) #f x m = ()

abstract val contains_const_on: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                  -> Lemma (requires (True))
                           (ensures (mem #k #f y d = contains #k #v #f y (const_on #k #v #f d x)))
                                    //(contains y (const_on d x) ==> Some.v (select p w) = x)))
                     [SMTPat (contains #k #v #f y (const_on #k #v #f d x))]
let contains_const_on (#k:Type) (#v:Type) #f d x y = ()
                     
abstract val select_const_on: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> x:v -> y:k
                     -> Lemma (requires (True))
                             (ensures (mem #k #f y d ==> (contains #k #v #f y (const_on #k #v #f d x) /\ Some.v (select #k #v #f y (const_on #k #v #f d x)) = x)))
                    [SMTPat (select #k #v #f y (const_on #k #v #f d x))]
let select_const_on (#k:Type) (#v:Type) #f d x y = ()

abstract val sel_rem1: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
              -> Lemma (requires True) (ensures select #k #v #f x
                                                (remove #k #v #f x m) = None)
                 [SMTPat (select #k #v #f x (remove #k #v #f x m))]
let sel_rem1 (#k:Type) (#v:Type) #f x m = ()

abstract val sel_rem2: #k:Type -> #v:Type -> #f:cmp k -> x:k -> x':k -> m:ordmap k v f
              -> Lemma (requires True) (ensures (x =!= x' ==>
                                                 select #k #v #f x'
                                                 (remove #k #v #f x m) = select #k #v #f x' m))
                 [SMTPat (select #k #v #f x' (remove #k #v #f x m))]
let sel_rem2 (#k:Type) (#v:Type) #f x x' m = ()

abstract val rem_upd: #k:Type -> #v:Type -> #f:cmp k -> x:k -> y:v -> x':k -> m:ordmap k v f
             -> Lemma (requires (True)) (ensures (x =!= x' ==>
                                                  Equal (update #k #v #f x y (remove #k #v #f x' m)) 
                                                        (remove #k #v #f x' (update #k #v #f x y m))))
                [SMTPat (update #k #v #f x y (remove #k #v #f x' m))]
let rem_upd (#k:Type) (#v:Type) #f x y x' m = ()
