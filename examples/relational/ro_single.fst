(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Bytes.fst FStar.List.fst xor.fst
  --*)
module Ro_Single
open FStar.List
open FStar.Bytes
open FStar.Heap
open Xor

type map (a:Type) (b:Type) = list (a * b)

type key = bytes
type tag = block

type alloc =
  | Hon: alloc
  | Adv: alloc (* a "ghost" field recording the first allocator for a given key *)

type log = map key (alloc * tag)

type state_hash =
  { bad: bool; (* set iff any allocation has failed, e.g. bumped into the other's table *)
    l:log }    (* the map ensures at most one entry per key *)

type log_monotone (s':state_hash) (s:state_hash) =
            (s'.bad ==> s.bad) /\
            (forall x. is_Some (assoc x s'.l) ==>
                    is_Some (assoc x s.l) /\ Some.v (assoc x s.l) = Some.v (assoc x s'.l))

assume val s : ref state_hash

assume val sample: unit -> Tot tag

let add_some t = Some t

val hash_hon : k:key -> ST (option tag)
                           (requires (fun h -> True))
                           (ensures (fun h' r h -> log_monotone (sel h' s) (sel h s) /\
                                                   ((sel h s).bad \/
                                                    is_Some r /\ is_Some (assoc k (sel h s).l) /\
                                                    Some.v #tag r = snd (Some.v (assoc k (sel h s).l)))))
let hash_hon k = match assoc k (!s).l with
  | Some (Hon, t) -> Some t
  | Some (Adv, t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = sample () in
                    s := {bad = (!s).bad; l= (k,(Hon, t))::(!s).l} ;
                    add_some t

val hash_adv : k:key -> ST (option tag)
                           (requires (fun h -> True))
                           (ensures (fun h' r h -> log_monotone (sel h' s) (sel h s) /\
                                                   ((sel h s).bad \/
                                                    is_Some r /\ is_Some (assoc k (sel h s).l) /\
                                                    Some.v #tag r = snd (Some.v (assoc k (sel h s).l)))))
let hash_adv k = match assoc k (!s).l with
  | Some (Adv, t) -> Some t
  | Some (Hon, t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = sample () in
                    s := {bad = (!s).bad; l= (k,(Adv, t))::(!s).l} ;
                    add_some t


assume val append : bytes -> bytes -> Tot bytes

val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

val encrypt_hon : k:bytes -> p:block
                  -> ST (option (block * block))
                  (requires (fun h -> True))
                  (ensures  (fun h' r h -> log_monotone (sel h' s) (sel h s) /\
                                             ((~ (sel h s).bad)  ==>
                                             is_Some r /\
                                             is_Some (assoc (append k (snd #block #block (Some.v r))) (sel h s).l) /\
                                             encrypt p (snd (Some.v (assoc (append k (snd #block #block (Some.v r))) (sel h s).l))) = fst (Some.v r))))
let encrypt_hon k p =
                  let r = sample () in
                  let kh = append k r in
                  let h  = hash_hon kh in
                  let st = !s in
                  let a = if is_Some h then(
                      assert(st.bad \/ is_Some(assoc kh st.l));
                      Some ((encrypt p (Some.v h)), r))
                    else None in
                  a

val decrypt_hon : k:bytes -> c:(block * block)
                  -> ST (option block)
                  (requires (fun h -> True))
                  (ensures  (fun h' r h -> log_monotone (sel h' s) (sel h s) /\
                                           ((~ (sel h s).bad /\
                                            is_Some (assoc(append k (snd c)) (sel h' s).l)
                                              ==> is_Some r /\
                                                  Some.v #block r = decrypt (fst c) (snd (Some.v (assoc (append k (snd c)) (sel h s).l)))))))
let decrypt_hon k (c, r) =
                  let kh = append k r in
                  let h  = hash_hon kh in
                  let a = if is_Some h then Some (decrypt c (Some.v h)) else None in
                  a
val correctness : k:bytes -> p:block
                   -> ST unit
                      (requires (fun h -> True))
                      (ensures  (fun h' r h -> log_monotone (sel h s) (sel h s)))

assume val arbitrary_actions : unit ->
                              ST unit (requires fun h -> True)
                                      (ensures  (fun h' r h -> log_monotone (sel h' s) (sel h s)))


let correctness k p =
                  let c = encrypt_hon k p in
                  arbitrary_actions ();
                  if is_Some c then
                    let p' = decrypt_hon k (Some.v c) in
                    let st = !s in
                    if not (st.bad) then
                      assert(is_Some p' /\ p = Some.v p')
