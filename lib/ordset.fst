(*--build-config
    other-files:list.fst ordset.fsi
 --*)

module OrdSet

opaque type total_order (a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)

type cmp (a:Type) = f:(a -> a -> Tot bool){total_order a f}

val sorted: #a:Type -> f:cmp a -> list a -> Tot bool
let rec sorted (#a:Type) f l = match l with
  | []       -> true
  | x::[]    -> true
  | x::y::tl -> f x y && x <> y && sorted f (y::tl)

type ordset (a:Type) (f:cmp a) = l:(list a){sorted f l}

let empty _ = []

val insert': #a:Type -> f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){is_Cons l /\ (Cons.hd l = x \/ (is_Cons s /\ Cons.hd l = Cons.hd s))})
let rec insert' f x s = match s with
  | []     -> [x]
  | hd::tl ->
    if x = hd then hd::tl
    else if f x hd then x::hd::tl
    else hd::(insert' f x tl)

let insert f x s = insert' f x s

let rec union f s1 s2 = match s1 with
  | []     -> s2
  | hd::tl -> union f tl (insert f hd s2)

let rec intersect f s1 s2 = match s1 with
  | []     -> []
  | hd::tl ->
    if List.mem hd s2 then
      insert f hd (intersect f tl s2)
    else
      intersect f tl s2

let mem f x s = List.mem x s

let choose f s = match s with
  | []   -> None
  | x::_ -> Some x

val remove': #a:Type -> f:cmp a -> x:a -> s:ordset a f
             -> Tot (l:(ordset a f){(is_Nil s ==> is_Nil l) /\
                                    (is_Cons s ==> Cons.hd s = x ==> l = Cons.tl s) /\
                                    (is_Cons s ==> Cons.hd s =!= x ==> (is_Cons l /\ Cons.hd l = Cons.hd s))})
let rec remove' f x s = match s with
  | []     -> []
  | hd::tl ->
    if x = hd then tl
    else hd::(remove' f x tl)

let remove f x s = remove' f x s

let size f s = List.length s

val eq_helper: #a:Type -> f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (is_Cons s /\ f x (Cons.hd s) /\ x =!= Cons.hd s))
                        (ensures (not (mem f x s))) (decreases (size f s))
let rec eq_helper f x (y::s) = match s with
  | []   -> ()
  | _::_ -> eq_helper f x s

val hd_unique: #a:Type -> f:cmp a -> s:ordset a f{is_Cons s}
               -> Lemma (requires (is_Cons s))
                        (ensures (not (mem f (Cons.hd s) (Cons.tl s))))
let hd_unique f (x::s) = match s with
  | []   -> ()
  | _::_ -> eq_helper f x s

let rec eq_lemma f s1 s2 = match s1, s2 with
  | [], []             -> ()
  | _::_, []           -> ()
  | [], _::_           -> ()
  | hd1::tl1, hd2::tl2 ->
    if hd1 = hd2 then
      (* hd_unique calls help us prove that forall x. mem f x tl1 = mem f x tl2 *)
      (* so that we can apply IH *)
      (hd_unique f s1; hd_unique f s2; eq_lemma f tl1 tl2)
    else if f hd1 hd2 then
      eq_helper f hd1 s2
    else
      eq_helper f hd2 s1

let mem_empty f = ()

let rec insert_lem f x s = match s with
  | []     -> ()
  | hd::tl -> if x = hd then () else insert_lem f x tl

let rec mem_union f s1 s2 x = match s1 with
  | []     -> ()
  | hd::tl -> mem_union f tl (insert f hd s2) x

let rec mem_intersect f s1 s2 x = match s1 with
  | []     -> ()
  | hd::tl -> mem_intersect f tl s2 x

let choose_lem f s = match s with
  | [] -> ()
  | _  ->  
    let Some e = choose f s in
    eq_lemma f s (insert f e (remove f e s))

let rec remove_lem f x s = match s with
  | []     -> ()
  | hd::tl -> if x = hd then hd_unique f s else remove_lem f x tl

let rec remove_size f x s = match s with
  | []     -> ()
  | hd::tl ->
    if x = hd then () else remove_size f x tl

(**********)

val insert_basic: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                  -> Lemma (ensures (mem f x (insert f x s)))
let insert_basic f x s = ()

val remove_basic: #a:Type -> f:cmp a -> x:a -> s:ordset a f
                  -> Lemma (ensures (not (mem f x (remove f x s))))
let remove_basic f x s = ()

val choose_basic: #a:Type -> f:cmp a -> s:ordset a f{s =!= empty f}
                  -> Lemma (ensures (is_Some (choose f s) /\ mem f (Some.v (choose f s)) s))
let choose_basic f s = ()
