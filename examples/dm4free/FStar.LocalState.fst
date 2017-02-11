module FStar.LocalState

#set-options "--print_universes"
type vect (a:Type0) : nat -> Type0 =
  | Nil : vect a 0
  | Cons : #n:nat -> hd:a -> tl:vect a n -> vect a (n+1)

let rec get #n #a (v:vect a n) (i:nat{i < n}) : a =
  if i = n-1 then Cons?.hd v else get (Cons?.tl v) i

let rec set #n #a (v:vect a n) (i:nat{i < n}) (x:a) : vect a n =
  if i = n-1
  then Cons x (Cons?.tl v)
  else Cons (Cons?.hd v) (set (Cons?.tl v) i x)

let rec insert #n #a (v:vect a n) (i:nat{i < n+1}) (x:a) : vect a (n+1) =
  if i = n then Cons x v
  else match v with | Cons hd tl -> Cons hd (insert tl i x)


let rec remove (#n:nat) #a (v:vect a (n+1)) (i:nat{i < n+1}) : vect a n =
  if i = n then Cons?.tl v
  else match v with | Cons hd tl ->
    let n' : nat = n -1 in  Cons hd (remove #n' #a tl i)



(* type count = | A | D | N *)
(* let left_count = function | A -> 0 | D -> 1 | N -> 2 *)
(* let right_count = function | A -> 1 | D -> 0 | N -> 2 *)
(* let left = List.fold_left left_count 0 *)
(* let right= List.fold_left right_count 0 *)

(* type mapping : nat -> nat -> Type = | Witness : (l:list count) -> mapping (left l) (right l) *)


type mapping (a:Type0) : nat -> nat -> Type0 =
  | MNil : mapping a 0 0
  | MCons : #n1:nat -> #n2:nat -> hd:a -> tl:mapping a n1 n2 -> mapping a (n1+1) (n2+1)
  | MAdd : #n1:nat -> #n2:nat -> hd:a -> tl:mapping a n1 n2 -> mapping a n1 (n2+1)
  | MRemove : #n1:nat -> #n2:nat -> tl:mapping a n1 n2 -> mapping a (n1+1) n2


let rec mget #n1 #n2 #a (v:mapping a n1 n2) (i:nat{i < n2}) : a =
  if i = n2-1
  then match v with
    | MCons hd _ -> hd
    | MAdd hd _ -> hd
    | MRemove tl -> mget tl i
  else match v with
    | MRemove tl -> mget tl i
    | MCons _ tl -> mget tl i
    | MAdd _ tl -> mget tl i

let rec mset #n1 #n2 #a (v:mapping a n1 n2) (i:nat{i < n2}) (x:a) : mapping a n1 n2 =
  if i = n2-1
  then match v with
    | MCons _ tl -> MCons x tl
    | MAdd _ tl -> MAdd x tl
    | MRemove tl -> MRemove (mset tl i x)
  else match v with
    | MRemove tl -> MRemove (mset tl i x)
    | MCons hd tl -> MCons hd (mset tl i x)
    | MAdd hd tl -> MAdd hd (mset tl i x)

let rec minsert #n1 #n2 #a (v:mapping a n1 n2) (i:nat{i < n2+1}) (x:a) : mapping a n1 (n2+1) =
    if i = n2
    then MAdd x v
    else match v with
      | MRemove tl -> MRemove (minsert tl i x)
      | MCons hd tl -> MCons hd (minsert tl i x)
      | MAdd hd tl -> MAdd hd (minsert tl i x)

let rec mremove #n1 (#n2:nat) #a (v:mapping a n1 (n2+1)) (i:nat{i < n2+1}) : mapping a n1 n2 =
  if i = n2
  then match v with
    | MCons hd tl -> MRemove tl
    | MAdd hd tl -> tl
    | MRemove tl -> MRemove (mremove tl i)
  else match v with
    | MRemove tl -> MRemove (mremove tl i)
    | MCons hd tl -> let n2' : nat = n2 - 1 in MCons hd (mremove #_ #n2' tl i)
    | MAdd hd tl -> let n2' : nat = n2 - 1 in MAdd hd (mremove #n1 #n2' tl i)

let rec mapping_to_vect0 (#n1 #n2:nat) (#a:Type0) (v:mapping a n1 n2)  : vect a n2 =
  match v with
    | MNil -> Nil
    | MCons hd tl -> Cons hd (mapping_to_vect0 tl)
    | MAdd hd tl -> Cons hd (mapping_to_vect0 tl)
    | MRemove tl -> mapping_to_vect0 tl


(* let rec mapping_to_vect_aux (#n1 #n2:nat) (#a:Type0) (v:mapping a n1 n2) (cont: n:nat -> vect a n -> (k:nat & vect a k)) : (k:nat & vect a k) = *)
(*   match v with *)
(*     | MNil -> cont 0 Nil *)
(*     | MCons hd tl -> mapping_to_vect_aux tl (fun n tl' -> cont (n+1) (Cons hd tl')) *)
(*     | MAdd hd tl -> mapping_to_vect_aux tl (fun n tl' -> cont (n+1) (Cons hd tl')) *)
(*     | MRemove tl -> mapping_to_vect_aux tl cont *)

(* let rec mapping_to_vect (#n1 #n2 : nat) (#a:Type0) (v:mapping a n1 n2) : (k:nat & vect a k) = *)
(*   mapping_to_vect_aux v Mkdtuple2 *)

let rec vect_to_mapping (#n:nat) (#a:Type0) (v:vect a n) : mapping a n n =
  match v with
    | Nil -> MNil
    | Cons hd tl -> MCons hd (vect_to_mapping tl)

let rec compose_mapping (#s:Type) (#n1 #n2 #n3:nat) (m1:mapping s n1 n2) (m2:mapping s n2 n3) : mapping s n1 n3
= let m1_m2 : mapping s n1 n2 * mapping s n2 n3 = m1, m2 in
  match m1_m2 with
  | MNil, MNil ->
    MNil
  | MCons hd1 tl1, MCons hd2 tl2 -> (* hd1= hd2 in the case we are interested in *)
    MCons hd1 (compose_mapping tl1 tl2)
  | MCons _ tl1, MRemove tl2 ->
    MRemove (compose_mapping tl1 tl2)
  | _, MAdd hd tl ->
    MAdd hd (compose_mapping m1 tl)
  | MRemove tl1, _ ->
    MRemove (compose_mapping tl1 m2)
  | MAdd hd1 tl1, MCons hd2 tl2 -> (* hd1= hd2 in the case we are interested in *)
    MAdd hd1 (compose_mapping tl1 tl2)
  | MAdd hd1 tl1, MRemove tl2 ->
    compose_mapping tl1 tl2

(* *)

type local_state0 (s:Type0) (a:nat -> Type0) (n:nat) =  v:vect s n -> k:nat & _:(a k) & mapping s n k

let return #s #a #n (x:a n) : local_state0 s a n = fun (v:vect s n) -> (|n, x, vect_to_mapping v|)
let bind #s #a #b #n (m:local_state0 s a n) (f: k:nat -> a k -> local_state0 s b k) : local_state0 s b n =
  fun (v : vect s n) ->
    let (| k, xk, mapk |) = m v in
    let (| k', yk', mapk' |) = f k xk (mapping_to_vect0 mapk) in
      (| k', yk', compose_mapping mapk mapk'|)

(* Operations on local_state0 *)

let const (a:Type0) : nat -> Type0 = fun n -> a

let read (s:Type0) (n:nat) (i:nat{i < n}) : local_state0 s (const s) n =
  fun v -> (| n, get v i, vect_to_mapping v |)

let write (s:Type0) (n:nat) (i:nat{i < n}) (x:s) : local_state0 s (const unit) n =
  fun v -> let v' = set v i x in (| n, (), vect_to_mapping v'|)

let alloc (s:Type0) (n:nat) (i:nat{i < n + 1}) (x:s) : local_state0 s (const unit) n =
  fun v -> (| n+1, (), minsert (vect_to_mapping v) i x |)

let dealloc (s:Type0) (n:nat) (i:nat{i < n + 1}) : local_state0 s (const unit) (n+1) =
  fun v -> (| n, (), mremove (vect_to_mapping v) i|)


(* DMFF translation of local_state0' *)
type local_state0' (s:Type0) (a:nat -> Type0) (n:nat) =
  v:vect s n -> M (k:nat & _:(a k) & mapping s n k)

type local_state1 (s:Type0) (a:nat -> Type0) (n:nat) =
  v:vect s n -> ((k:nat & _:(a k) & mapping s n k) -> GTot Type0) -> GTot Type0

let return1 #s #a #n (x:a n) : local_state1 s a n = fun (v:vect s n) p -> p (|n, x, vect_to_mapping v|)
let bind1 #s #a #b #n (m:local_state1 s a n) (f: k:nat -> a k -> local_state1 s b k) : local_state1 s b n =
  fun (v : vect s n) p ->
  m v (fun (| k, xk, mapk |) ->
    f k xk (mapping_to_vect0 mapk) (fun (| k', yk', mapk' |) ->
      p (| k', yk', compose_mapping mapk mapk'|)))

type local_state2 (s:Type0) (a:nat -> Type0) (n:nat) (spec:local_state1 s a n) =
  v:vect s n -> PURE (k:nat & _:(a k) & mapping s n k) (spec v)

let return2 #s #a #n (x:a n) : local_state2 s a n (return1 #s #a #n x) = fun (v:vect s n) -> (|n, x, vect_to_mapping v|)

#set-options "--admit_smt_queries true"
let bind2 #s #a #b #n (specm:local_state1 s a n) (m:local_state2 s a n specm) (specf: k:nat -> a k -> local_state1 s b k) (f: k:nat -> x:a k -> local_state2 s b k (specf k x))
  : local_state2 s b n (bind1 #s #a #b #n specm specf) =
  fun (v : vect s n) ->
    let (| k, xk, mapk |)= m v in
    let (| k', yk', mapk' |) = f k xk (mapping_to_vect0 mapk) in
      (| k', yk', compose_mapping mapk mapk'|)
#set-options "--admit_smt_queries false"

let ls_pre (s:Type0) (n:nat) = vect s n -> GTot Type0
let ls_post (s:Type0) (a:nat -> Type0) (n:nat) = (k:nat & _:(a k) & mapping s n k) -> GTot Type0
let ls_wp (s:Type0) (a:nat -> Type0) (n:nat) = ls_post s a n -> Tot (ls_pre s n)

unfold
let ls_return (s:Type0) (a:nat -> Type0) (n:nat) (x:a n) (p:ls_post s a n) : Tot (ls_pre s n) =
  fun v -> return1 #s #a #n x v p

unfold
let ls_bind_wp (s:Type0) (r1:range) (a b:nat -> Type0) (n:nat) (wp1:ls_wp s a n) (wp2: k:nat -> a k -> GTot (ls_wp s b k)) (p:ls_post s b n) (v:vect s n) =
  bind1 #s #a #b #n (fun v p -> wp1 p v) (fun k a v p -> wp2 k a p v) v p

unfold
let ls_if_then_else (s:Type0) (a:nat -> Type0) (p:nat -> Type0) (n:nat) (wp_then:ls_wp s a n) (wp_else:ls_wp s a n) (post:ls_post s a n) (v:vect s n) =
  l_ITE (p n) (wp_then post v) (wp_else post v)

unfold
let ls_ite_wp (s:Type0) (a:nat -> Type0) (n:nat) (wp:ls_wp s a n) (post:ls_post s a n) (v:vect s n) =
  (forall (k:ls_post s a n). (forall (x:(k:nat & _:a k & mapping s n k)). {:pattern (guard_free (k x))} k x <==> post x) ==> wp k v)

unfold
let ls_stronger (s:Type0) (a:nat -> Type0) (n:nat) (wp1 wp2:ls_wp s a n) =
  forall (p:ls_post s a n) (v:vect s n). wp1 p v ==> wp2 p v

unfold
let ls_close_wp (s:Type0) (a b:nat -> Type0) (wp: k:nat -> b k -> GTot (ls_wp s a k)) (n:nat) (p:ls_post s a n) (v:vect s n) =
  forall (xb:b n). wp n xb p v

unfold
let ls_assert_p (s:Type0) (a:nat -> Type0) (p:nat -> Type0) (n:nat) (wp:ls_wp s a n) (q:ls_post s a n) (v:vect s n) =
  p n /\ wp q v

unfold
let ls_assume_p (s:Type0) (a:nat -> Type0) (p:nat -> Type0) (n:nat) (wp:ls_wp s a n) (q:ls_post s a n) (v:vect s n) =
  p n ==> wp q v

unfold
let ls_null_wp (s:Type0) (a:nat -> Type0) (n:nat) (p:ls_post s a n) (v:vect s n) =
  forall x. p x

unfold
let ls_trivial (s:Type0) (a:nat -> Type0) (n:nat) (wp:ls_wp s a n) =
  forall v. wp (fun _ -> True) v

(* new_effect { *)
(*   LS (s:Type0) : result:(nat -> Type) -> n:nat -> wp:ls_wp s (a n) n -> Effect *)
(*   with *)

(*   } *)

(* Algebraic presentation *)

noeq type free_local_state (s:Type0) (a:nat -> Type0) : nat -> Type0 =
  | Return : #n:nat -> a n -> free_local_state s a n
  | Write : #n:nat -> i:nat{i < n} -> s -> free_local_state s a n -> free_local_state s a n
  | Read : #n:nat -> i:nat{i < n} -> (s -> free_local_state s a n) -> free_local_state s a n
  | Alloc : #n:nat -> i:nat{i < n+1} -> s -> (s -> free_local_state s a (n+1)) -> free_local_state s a n
  | Dealloc : #n:nat -> i:nat{i < n+1} -> free_local_state s a n -> free_local_state s a (n+1)
  (* | Swap : n:nat -> i:nat{i < n} -> j:nat{j < i} -> free_local_state s a n -> free_local_state s a n *)

assume val precede_app (#a #b : Type) (f : a -> Tot b) (x:a)
  : Lemma (requires True) (ensures (f x << f))
let apply (#a #b : Type) (f : a -> Tot b) (x: a)
  : Tot (r:b{r << f})
= precede_app f x ; f x


let rec eval0 (#s:Type0) (#a:nat -> Type0) #n #n0 (m : free_local_state s a n)
: Tot (mapping s n0 n -> (k:nat & _:(a k) & mapping s n0 k)) (decreases m)
= fun v -> match m with
        | Return xa -> (|n, xa, v|)
        | Write i si m -> eval0 m (mset v i si)
        | Read i f -> eval0 (apply f (mget v i)) v
        | Alloc i sinit f -> eval0 (apply f sinit) (minsert v i sinit)
        | Dealloc i m -> eval0 m (mremove v i)


let rec eval (#s:Type0) (#a:nat -> Type0) #n (m:free_local_state s a n) (v:vect s n)
: (k:nat & _:(a k) & mapping s n k) =
  eval0 m (vect_to_mapping v)

let rec eval_vect (#s:Type0) (#a:nat -> Type0) #n (m : free_local_state s a n)
: Tot (vect s n -> (k:nat & _:(a k) & vect s k)) (decreases m)
= fun v -> match m with
        | Return xa -> (|n, xa, v|)
        | Write i si m -> eval_vect m (set v i si)
        | Read i f -> eval_vect (apply f (get v i)) v
        | Alloc i sinit f -> eval_vect (apply f sinit) (insert v i sinit)
        | Dealloc i m -> eval_vect m (remove v i)


let rec build_output #s #a (#n1 #n2 i:nat) (v:mapping s n1 n2) (m:free_local_state s a (n2+i)) : free_local_state s a (n1+i) * (k:nat{k <= n1}) =
  match v with
  | MNil -> m, 0
  | MCons hd tl -> let m, k = build_output (i+1) tl m in Write k hd m, k+1
  | MAdd hd tl -> let m, k = build_output (i+1) tl m in let n' = n1+i in Alloc #s #a #n' k hd (fun s -> m), k
  | MRemove tl -> let m, k = build_output i tl m in Dealloc k m, k+1


let rec build_input #s #a #n (f:(vect s n -> free_local_state s a n)) (k:nat{k <= n}) : Tot (vect s k -> free_local_state s a n) (decreases (n - k))
= if k = n
  then f
  else let f = build_input f (k+1) in
    fun v -> Read k (fun sk -> f (insert v k sk))


let build_expr #s #a #n (f:vect s n -> Tot (k:nat & _:(a k) & mapping s n k))
: free_local_state s a n
= let output (v : vect s n) : free_local_state s a n =
    match f v with
    | (| k, xak, v' |) -> fst (build_output #s #a #n #k 0 v' (Return xak))
  in
  build_input#s #a #n output 0 Nil

let rec is_normalized_input #s #a #n k (m:free_local_state s a n) : Tot Type0 (decreases m) =
  if k = n then is_normalized_output k m
  else match m with
    | Read i f -> i == k /\ (forall (s0:s). is_normalized_input (k+1) (apply f s0))
    | _ -> False

and is_normalized_output #s #a #n k (m:free_local_state s a m) : Tot Type0 (decreases m) =
  if k = 0 then b2t (Return? m)
  else match m with
  | Alloc i si f -> i == k /\ is_normalized_output k (apply f si)
  | Write i si m -> i == k /\ is_normalized_output (k-1) m
  | Dealloc i m -> i == k /\ is_normalized_output (k-1) m
  | _ -> False

let is_normalized #s #a #n (m:free_local_state s a n) = is_normalized_input 0 m

let local_state (s:Type) (a:nat -> Type) (n:nat) = m:(free_local_state s a n){is_normalized m}


(* let rec is_normalized_alloc i n acc = function *)
(*   | Alloc i' f -> i' >= i /\ (forall (s0:s). is_normalized_alloc (i'+1) (n+1) (i'::acc) (f s0)) *)
(*   | m -> is_normalized_read 0 n acc m *)

(* and is_normalized_read i n l = function *)
(*   | Read i' f -> i' = i /\ (forall (s0:s). is_normalized_read (i+1) n l (f s0)) *)
(*   | m -> i = n /\ is_normalized_write n n l m *)

(* and is_normalized_write i n l = function *)
(*   | Write i' _ m -> i = i'+1 /\ is_normalized_write i' n l m *)
(*   | m -> i = 0 /\ is_normalized_dealloc (n-1) l m *)

(* and is_normalized_dealloc i allocs = function *)
(*   | Dealloc i' m -> i >= i' /\ not (List.contains i' allocs) /\ is_normalized_dealloc (i-1) m *)
(*   | Return x -> True *)
(*   | _ -> False *)

(* let is_normalized #a #a #n (m:free_local_state s a n) = *)
(*   is_normalized_alloc 0 n m *)


(* let local_state (s:Type0) (a:nat -> Type) (n:nat) : Type = m:(free_local_state s a n){is_normalized m} *)

(* let return (s:Type0) (a:nat -> Type) (x: n:nat -> a n) : n:nat -> local_state s a n = *)
(*   fun n -> *)
(*     let rec build_return i acc = *)
(*       if i = n then acc else Read #n i (fun si -> build_return (i+1) (Write #n i si acc)) *)
(*     in *)
(*     build_return (Return #n (x n)) *)

(* (\* let bind (s:Type0) *\) *)
(* (\*          (a b:nat -> Type) *\) *)
(* (\*          (x:n:nat -> local_state s a n) *\) *)
(* (\*          (f: n:nat -> a n -> local_state s b n) *\) *)
(* (\*          : n:nat -> local_state s b n = *\) *)



(* (\* let rec range step n stop acc = *\) *)
(* (\*   if stop n then acc else range step (n+step) stop n::acc *\) *)

(* (\* let upto i j = range (-1) j (fun k -> k <= i) [] *\) *)
(* (\* let downto i j = range 1 j (fun k -> k >= i) [] *\) *)






(* (\* (\\* Normalization does not seems to be computable for arbitrary state *\\) *\) *)
(* (\* (\\* (see case of read) so we take s = bool                            *\\) *\) *)

(* (\* let rec merge l1 l2 = match l1, l2 with *\) *)
(* (\*   | [], l *\) *)
(* (\*   | l, [] -> l *\) *)
(* (\*   | x::xs, y::ys -> *\) *)
(* (\*     match () with *\) *)
(* (\*     | _ when x = y -> x::merge xs ys *\) *)
(* (\*     | _ when x < y -> x::merge xs l2 *\) *)
(* (\*     | _ when x > y -> y::merge l1 ys *\) *)

(* (\* let rec push i = function *\) *)
(* (\*   | [] -> [i] *\) *)
(* (\*   | x :: xs -> if x < i then x :: push i xs else i :: xs *\) *)

(* (\* let rec pop i = function *\) *)
(* (\*   | [] -> [] *\) *)
(* (\*   | x :: xs if x < i then x :: pop i xs else List.map (fun n -> n+1) xs *\) *)

(* (\* let rec normalize_alloc = function *\) *)
(* (\*   | Return _ -> [] *\) *)
(* (\*   | Write _ m -> normalize_count_alloc m *\) *)
(* (\*   | Read f -> merge (normalize_count_alloc (f true)) (normalize_count_alloc (f false)) *\) *)
(* (\*   | Alloc i f -> push i (merge (normalize_count_alloc (f true)) (normalize_count_alloc (f false))) *\) *)
(* (\*   | Dealloc _ m -> pop i (normalize_count_alloc m) *\) *)

(* (\* let normalize_aux_finalize output dealloc_pos return_value = *\) *)
(* (\*   Return return *\) *)
(* (\*     |> List.fold_left (fun r i -> Dealloc i r) dealloc_pos *\) *)
(* (\*     |> List.fold_lefti (fun r x i -> Write i x r) output *\) *)
