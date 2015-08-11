(*--build-config
 --*)
module OrdMap

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2) (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3) (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                (* totality      *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val sorted: #a:Type -> f:cmp a -> list a -> Tot bool
let rec sorted (#a:Type) f l = match l with
  | []       -> true
  | x::[]    -> true
  | x::y::tl -> f x y && x <> y && sorted f (y::tl)

type ordset (a:Type) (f:cmp a) = l:(list a){sorted f l}

val mem: 'a -> list 'a -> Tot bool //x:'a -> l:list 'a -> b:bool{b==true <==> In x l}
let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

type map_t (k:Type) (v:Type) (f:cmp k) (d:ordset k f) =
  g:(k -> Tot (option v)){(forall x. (mem x d = is_Some (g x)))}

type ordmap: key:Type -> value:Type -> cmp key -> Type =
  | Mk_map: #k:Type -> #v:Type -> #f:cmp k -> d:ordset k f -> m:map_t k v f d -> ordmap k v f

val select  : #key:Type -> #value:Type -> #f:cmp key -> k:key
              -> m:ordmap key value f -> Tot (option value)
let select (#k:Type) (#v:Type) #f x (Mk_map d m) = m x

val contains: #key:Type -> #value:Type -> #f:cmp key -> key -> ordmap key value f
              -> Tot bool
let contains (#k:Type) (#v:Type) #f x (Mk_map s g) = mem x s

val sel_contains: #k:Type -> #v:Type -> #f:cmp k -> x:k -> m:ordmap k v f
      -> Lemma (requires (True))
               (ensures (contains #k #v #f x m = is_Some (select #k #v #f x m)))
#reset-options
let sel_contains (#k:Type) (#v:Type) #f x m = ()
