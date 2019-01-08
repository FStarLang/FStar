(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.DM4F.IntStore

(* open FStar.DM4F.IntStoreAux *)
open FStar.Seq


type id = nat
type heap = seq int
let in_ (x:id) (store:heap) = x < length store

(* TODO : Try to use [either a exn] instead of [option] *)
type int_store (a:Type) = heap -> M (option a * heap)
let return_is (a:Type) (x:a) : int_store a = fun store -> Some x, store
let bind_is (a b : Type) (x:int_store a) (f: a -> int_store b) : int_store b =
  fun store ->
  let (z, store') = x store in
    match z with
    | None -> None, store'
    | Some xa -> f xa store'

let get () : int_store (heap) = fun store -> Some store, store
let put s : int_store unit = fun _ -> Some (), s

(* DM4F does not handle polymorphic types yet so we go around this limitation *)
(* by returning an inhabitant of False and define a second polymorphic raise_ afterwards *)
let raise_impl () : int_store False = fun store -> None, store

total reifiable reflectable new_effect {
  INT_STORE : a:Type -> Effect
  with repr   = int_store
     ; bind   = bind_is
     ; return = return_is
     ; get   = get
     ; put    = put
     ; raise_ = raise_impl
}

effect IntStore (a:Type) (pre:INT_STORE?.pre) (post: heap -> option a -> heap -> GTot Type0) =
  INT_STORE a (fun l0 p -> pre l0 /\ (forall x l1. pre l0 /\ post l0 x l1 ==> p (x, l1)))

effect IS (a:Type) =
  INT_STORE a (fun (l0:heap) (p:((option a * heap) -> Type0)) -> forall (x:(option a * heap)). p x)

(* TODO : having a in Type *and*  induces a Failure("Universe variable not found") *)
(* whenever we try to normalize-reify it (see below in xxx for instance) *)

let raise_ (#a:Type0) ()
  : IntStore a (fun _ -> True) (fun l0 x l1 -> l0 == l1 /\ None? x)
= let x = INT_STORE?.raise_ () in begin match x with end


(* KM : Would it be possible to merge both read by adding a boolean flag *)
(* deciding whether the check on the index i must be static or dynamic ? *)

let read (i:id)
  : INT_STORE int
    (fun s p ->
      if i `in_` s
      then p (Some (index s i), s)
      else p (None, s))
=
  let store = IS?.get () in
  if i `in_` store
  then index store i
  else raise_ ()


  let write (i:id) (x:int)
  : INT_STORE unit
    (fun s p ->
      if i `in_` s
      then p (Some (),upd s i x)
      else p (None, s))
=
  let store = IS?.get () in
  if i `in_` store
  then IS?.put (upd store i x)
  else raise_ ()


let read_tot (i:id)
  : INT_STORE int (fun s0 p -> i `in_` s0 /\ p (Some (index s0 i), s0))
  (* KM : The following pre-post condition is not accepted *)
  (* It may be that IntStore is wrongly defined *)
  (* : IntStore int *)
  (*   (requires (fun s0 -> i `in_` s0)) *)
  (*   (ensures (fun s0 x s1 -> s0 `equals` s1 /\ i `in_` s1 /\ x = Some (index s1 i))) *)
=
  let store = IS?.get () in
  index store i


let write_tot (i:id) (x:int)
  : INT_STORE unit (fun s0 p -> i `in_` s0 /\ p (Some (), upd s0 i x))
=
  let store = IS?.get () in
  IS?.put (upd store i x)

(* assume val r : id *)
(* assume val store : heap *)

(* (\* KM : Is there any way to assume that r `in_` store so that it reduces in the normalizer ? *\) *)
(* let xxx = reify (read r) store *)

let total_read_lemma (store:heap) (r:id)
  : Lemma (requires r `in_` store) (ensures Some? (fst (reify (read r) store)))
= ()

let total_write_lemma (store:heap) (r:id) (x:int)
  : Lemma (requires r `in_` store) (ensures Some? (fst (reify (write r x) store)))
= ()


let read_write_lemma1 (store:heap) (r:id) (x:int)
    : Lemma (requires (r `in_` store))
      (ensures (r `in_` store /\ normalize_term (fst (reify (let () = write_tot r x in read_tot r) store)) == Some x))
= ()

(* Need indexed effects to have the following go through... *)

(* type heap_n n = h:heap{length h = n} *)

(* effect INT_STORE_N (n:nat) (a:Type) (wp:(heap_n n -> (option a -> h:heap_n n -> GTot Type0) -> GTot Type0)) = *)
(*   INT_STORE a (fun l0 p -> length l0 = n /\ wp l0 (fun x l1 -> p (x,l1))) *)

(*  *)
(* let read_n (#n:nat) (i:id) *)
(*   : INT_STORE_N n int *)
(*     (fun l0 p -> i < n /\ p (Some (index l0 i)) l0) *)
(* = index (IS?.get ()) i *)

(*  *)
(* let write_n (#n:nat) (i:id) (x:int) *)
(*   : INT_STORE_N n int *)
(*     (fun l0 p -> i < n /\ p (Some ()) (upd l0 i x)) *)
(* = IS?.put (upd (IS?.get ()) i x) *)

