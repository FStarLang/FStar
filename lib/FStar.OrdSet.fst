(*--build-config
    options:;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.List.Tot.fst FStar.ListProperties.fst 
 --*)

module FStar.OrdSet

type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)   (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val sorted: #a:Type -> f:cmp a -> list a -> Tot bool
let rec sorted (#a:Type) f l = match l with
  | []       -> true
  | x::[]    -> true
  | x::y::tl -> f x y && x <> y && sorted f (y::tl)

abstract type ordset (a:Type) (f:cmp a) = l:(list a){sorted f l}
abstract val empty     : #a:Type -> #f:cmp a -> Tot (ordset a f)
abstract val union     : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
abstract val intersect : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

abstract val mem       : #a:Type -> #f:cmp a -> a -> s:ordset a f -> Tot bool
abstract val choose    : #a:Type -> #f:cmp a -> s:ordset a f -> Tot (option a)
abstract val remove    : #a:Type -> #f:cmp a -> a -> ordset a f -> Tot (ordset a f)

abstract val size      : #a:Type -> #f:cmp a -> ordset a f -> Tot nat

abstract val subset    : #a:Type -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
abstract val singleton : #a:Type -> #f:cmp a -> a -> Tot (ordset a f)


let mem (#a:Type) #f x s = List.Tot.mem x s

val set_props:
  #a:Type -> #f:cmp a -> s:ordset a f{is_Cons s}
  -> Lemma (requires (True))
          (ensures (forall x. mem #a #f x (Cons.tl s) ==> (f (Cons.hd s) x /\ Cons.hd s =!= x)))
let rec set_props (#a:Type) #f s = match s with
  | x::tl -> if tl = [] then () else set_props #a #f tl

val hd_unique: #a:Type -> #f:cmp a -> s:ordset a f{is_Cons s}
               -> Lemma (requires (is_Cons s))
                       (ensures (not (mem #a #f (Cons.hd s) (Cons.tl s))))
let hd_unique (#a:Type) #f s = set_props #a #f s

let empty (#a:Type) #f = []

val insert': #a:Type -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){is_Cons l /\
                                    (Cons.hd l = x \/
                                    (is_Cons s /\ Cons.hd l = Cons.hd s))})
let rec insert' (#a:Type) #f x s = match s with
  | []     -> [x]
  | hd::tl ->
    if x = hd then hd::tl
    else if f x hd then x::hd::tl
    else hd::(insert' #_ #f x tl)

let rec union (#a:Type) #f s1 s2 = match s1 with
  | []     -> s2
  | hd::tl -> union #_ #f tl (insert' #_ #f hd s2)

let rec intersect (#a:Type) #f s1 s2 = match s1 with
  | []     -> []
  | hd::tl ->
    if mem #_ #f hd s2 then
      insert' #_ #f hd (intersect #_ #f tl s2)
    else
      intersect #_ #f tl s2

let choose (#a:Type) #f s = match s with
  | []   -> None
  | x::_ -> Some x

val remove': #a:Type -> #f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){(is_Nil s ==> is_Nil l) /\
                                    (is_Cons s ==> Cons.hd s = x ==> l = Cons.tl s) /\
                                    (is_Cons s ==> Cons.hd s =!= x ==> (is_Cons l /\ Cons.hd l = Cons.hd s))})
let rec remove' (#a:Type) #f x s = match s with
  | []     -> []
  | hd::tl ->
    if x = hd then tl
    else hd::(remove' #_ #f x tl)

let remove (#a:Type) #f x s = remove' #_ #f x s

let size (#a:Type) #f s = List.Tot.length s

let rec subset (#a:Type) #f s1 s2 = match s1, s2 with
  | [], _          -> true
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset #a #f tl tl'
    else if f hd hd' && not (hd = hd') then false
    else subset #a #f s1 tl'
  | _, _           -> false

let singleton (#a:Type) #f x = [x]

type Equal (#a:Type) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) =
  (forall x. mem #_ #f x s1 = mem #_ #f x s2)

val eq_lemma: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (Equal s1 s2))
                       (ensures (s1 = s2))
                 [SMTPatT (Equal s1 s2)]

val mem_empty: #a:Type -> #f:cmp a -> x:a
               -> Lemma (requires True) (ensures (not (mem #a #f x (empty #a #f))))
                  [SMTPat (mem #a #f x (empty #a #f))]

val mem_singleton: #a:Type -> #f:cmp a -> x:a -> y:a
                   -> Lemma (requires True)
                            (ensures (mem #a #f y (singleton #a #f x)) = (x = y))
                      [SMTPat (mem #a #f y (singleton #a #f x))]

val mem_union: #a:Type -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
               -> Lemma (requires True)
                        (ensures (mem #a #f x (union #a #f s1 s2) =
                                  (mem #a #f x s1 || mem #a #f x s2)))
                  [SMTPat (mem #a #f x (union #a #f s1 s2))]

val mem_intersect: #a:Type -> #f:cmp a -> x:a -> s1:ordset a f -> s2:ordset a f
                   -> Lemma (requires True)
                            (ensures (mem #a #f x (intersect s1 s2) =
                                      (mem #a #f x s1 && mem #a #f x s2)))
                      [SMTPat (mem #a #f x (intersect #a #f s1 s2))]

val mem_subset: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures  (subset #a #f s1 s2 <==>
                                    (forall x. mem #a #f x s1 ==> mem #a #f x s2)))
                   [SMTPat (subset #a #f s1 s2)]

val choose_empty: #a:Type -> #f:cmp a
                  -> Lemma (requires True) (ensures (is_None (choose #a #f (empty #a #f))))
                     [SMTPat (choose #a #f (empty #a #f))]

(* TODO: FIXME: Pattern does not contain all quantified vars *)
val choose_s: #a:Type -> #f:cmp a -> s:ordset a f
              -> Lemma (requires (not (s = (empty #a #f))))
                       (ensures (is_Some (choose #a #f s) /\
                                 s = union #a #f (singleton #a #f (Some.v (choose #a #f s)))
                                                 (remove #a #f (Some.v (choose #a #f s)) s)))
                 [SMTPat (choose #a #f s)]

val mem_remove: #a:Type -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures (mem #a #f x (remove #a #f y s) =
                                   (mem #a #f x s && not (x = y))))
                   [SMTPat (mem #a #f x (remove #a #f y s))]

val eq_remove: #a:Type -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (not (mem #a #f x s)))
                        (ensures (s = remove #a #f x s))
                  [SMTPat (remove #a #f x s)]

val size_empty: #a:Type -> #f:cmp a -> s:ordset a f
                -> Lemma (requires True) (ensures ((size #a #f s = 0) = (s = empty #a #f)))
                  [SMTPat (size #a #f s)]
                   
val size_remove: #a:Type -> #f:cmp a -> y:a -> s:ordset a f
                 -> Lemma (requires (mem #a #f y s))
                          (ensures (size #a #f s = size #a #f (remove #a #f y s) + 1))
                    [SMTPat (size #a #f (remove #a #f y s))]

val size_singleton: #a:Type -> #f:cmp a -> x:a
                    -> Lemma (requires True) (ensures (size #a #f (singleton #a #f x) = 1))
                       [SMTPat (size #a #f (singleton #a #f x))]
                       
private val eq_helper: #a:Type -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (is_Cons s /\ f x (Cons.hd s) /\ x =!= Cons.hd s))
                       (ensures (not (mem #a #f x s)))
let eq_helper (#a:Type) #f x (y::s) = set_props #a #f (y::s)

let rec eq_lemma (#a:Type) #f s1 s2 = match s1, s2 with
  | [], []             -> ()
  | _::_, []           -> ()
  | [], _::_           -> ()
  | hd1::tl1, hd2::tl2 ->
    if hd1 = hd2 then
      (* hd_unique calls help us prove that forall x. mem f x tl1 = mem f x tl2 *)
      (* so that we can apply IH *)
      (hd_unique #_ #f s1; hd_unique #_ #f s2; eq_lemma #_ #f tl1 tl2)
    else if f hd1 hd2 then
      eq_helper #_ #f hd1 s2
    else
      eq_helper #_ #f hd2 s1

let mem_empty (#a:Type) #f x = ()

let mem_singleton (#a:Type) #f x y = ()

private val insert_mem: #a:Type -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires (True))
                         (ensures (mem #a #f y (insert' #a #f x s) =
                                   (x = y || mem #a #f y s)))
let rec insert_mem (#a:Type) #f x y s = match s with
  | []     -> ()
  | hd::tl ->
    if x = hd then ()
    else if f x hd then ()
    else insert_mem #_ #f x y tl

let rec mem_union (#a:Type) #f x s1 s2 = match s1 with
  | []     -> ()
  | hd::tl ->
    mem_union #_ #f x tl (insert' #_ #f hd s2); insert_mem #_ #f hd x s2

let rec mem_intersect (#a:Type) #f x s1 s2 = match s1 with
  | []     -> ()
  | hd::tl ->
    let _ = mem_intersect #_ #f x tl s2 in
    if mem #_ #f hd s2 then insert_mem #_ #f hd x (intersect #_ #f tl s2) else ()

private val subset_implies_mem:
  #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures (subset #a #f s1 s2 ==> (forall x. mem #a #f x s1 ==>
                                                mem #a #f x s2)))
let rec subset_implies_mem (#a:Type) #f s1 s2 = match s1, s2 with
  | [], _          -> ()
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset_implies_mem #a #f tl tl'
    else subset_implies_mem #a #f s1 tl'
  | _, _           -> ()

private val mem_implies_subset:
  #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
  -> Lemma (requires (True))
          (ensures ((forall x. mem #a #f x s1 ==> mem #a #f x s2) ==> subset #a #f s1 s2))
let rec mem_implies_subset (#a:Type) #f s1 s2 = match s1, s2 with
  | [], [] -> ()
  | _::_, [] -> ()
  | [], _::_ -> ()
  | hd::tl, hd'::tl' ->
    set_props #a #f s1; set_props #a #f s2;

    if f hd hd' && hd = hd' then
      mem_implies_subset #a #f tl tl'
    else if f hd hd' && not (hd = hd') then
      ()
    else mem_implies_subset #a #f s1 tl'
    
let mem_subset (#a:Type) #f s1 s2 =
  subset_implies_mem #a #f s1 s2; mem_implies_subset #a #f s1 s2

let choose_empty (#a:Type) #f = ()

let choose_s (#a:Type) #f s =
  let Some e = choose #_ #f s in
  cut (Equal #a #f s (insert' #a #f e (remove #a #f e s)))

let rec mem_remove (#a:Type) #f x y s = match s with
  | []     -> ()
  | hd::tl -> if y = hd then hd_unique #_ #f s else mem_remove #_ #f x y tl

let rec eq_remove (#a:Type) #f x s = match s with
  | []    -> ()
  | _::tl -> eq_remove #_ #f x tl

let size_empty (#a:Type) #f s = ()

let rec size_remove (#a:Type) #f x s = match s with
  | hd::tl ->
    if x = hd then () else size_remove #_ #f x tl

let rec size_singleton (#a:Type) #f x = ()

val subset_size: #a:Type -> #f:cmp a -> x:ordset a f -> y:ordset a f
                 -> Lemma (requires (subset #a #f x y))
 	                  (ensures (size #a #f x <= size #a #f y))
	           [SMTPat (subset #a #f x y)]
let rec subset_size (#a:Type) #f x y = match x, y with
  | [], _          -> ()
  | hd::tl, hd'::tl' ->
    if f hd hd' && hd = hd' then subset_size #a #f tl tl'
    else subset_size #a #f x tl'

(**********)

(* TODO:FIXME: implement *)
assume val size_union: #a:Type -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures ((size #a #f (union #a #f s1 s2) >= size #a #f s1) &&
                                   (size #a #f (union #a #f s1 s2) >= size #a #f s2)))
                         [SMTPat (size #a #f (union #a #f s1 s2))]

