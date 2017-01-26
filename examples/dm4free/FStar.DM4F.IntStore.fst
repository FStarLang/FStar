module FStar.DM4F.IntStore

(* open FStar.DM4F.IntStoreAux *)
open FStar.Seq

type int_store (a:Type) = seq int -> M (option a * seq int)
let return_is (a:Type) (x:a) : int_store a = fun store -> Some x, store
let bind_is (a b : Type) (x:int_store a) (f: a -> int_store b) : int_store b =
  fun store ->
  let (z, store') = x store in
    match z with
    | None -> None, store'
    | Some xa -> f xa store'

let get () : int_store (seq int) = fun store -> Some store, store
let put s : int_store unit = fun _ -> Some (), s

(* DM4F does not handle polymorphic types yet so we go around this limitation *)
(* by returning an inhabitant of False and define a second polymorphic raise_ afterwards *)
let raise_impl () : int_store False = fun store -> None, store

total reifiable reflectable new_effect_for_free {
  INT_STORE : a:Type -> Effect
  with repr   = int_store
     ; bind   = bind_is
     ; return = return_is
  and effect_actions
       get   = get
     ; put    = put
     ; raise_ = raise_impl
}

effect IntStore (a:Type) (pre:INT_STORE?.pre) (post: seq int -> option a -> seq int -> GTot Type0) =
  INT_STORE a (fun l0 p -> pre l0 /\ (forall x l1. pre l0 /\ post l0 x l1 ==> p (x, l1)))

effect IS (a:Type) =
  INT_STORE a (fun (l0:seq int) (p:((option a * seq int) -> Type0)) -> forall (x:(option a * seq int)). p x)

(* TODO : having a in Type *and* reifiable induces a Failure("Universe variable not found") *)
(* whenever we try to normalize-reify it (see below in xxx for instance) *)
reifiable
let raise_ (#a:Type0) ()
  : IntStore a (fun _ -> True) (fun l0 x l1 -> l0 == l1 /\ None? x)
= let x = INT_STORE?.raise_ () in begin match x with end

reifiable
let read (i:nat)
  : INT_STORE int
    (fun s p ->
      if i < length s
      then p (Some (index s i), s)
      else p (None, s))
=
  let store = IS?.get () in
  if i < length store
  then index store i
  else raise_ ()

reifiable
  let write (i:nat) (x:int)
  : INT_STORE unit
    (fun s p ->
      if i < length s
      then p (Some (),upd s i x)
      else p (None, s))
=
  let store = IS?.get () in
  if i < length store
  then IS?.put (upd store i x)
  else raise_ ()

reifiable
let read_tot (i:nat)
  : INT_STORE int (fun s0 p -> i < length s0 /\ p (Some (index s0 i), s0))
  (* KM : The following pre-post condition is not accepted *)
  (* It may be that IntStore is wrongly defined *)
  (* : IntStore int *)
  (*   (requires (fun s0 -> i < length s0)) *)
  (*   (ensures (fun s0 x s1 -> s0 `equals` s1 /\ i < length s1 /\ x = Some (index s1 i))) *)
=
  let store = IS?.get () in
  index store i

reifiable
let write_tot (i:nat) (x:int)
  : INT_STORE unit (fun s0 p -> i < length s0 /\ p (Some (), upd s0 i x))
=
  let store = IS?.get () in
  IS?.put (upd store i x)

(* assume val r : nat *)
(* assume val store : seq int *)

(* (\* KM : Is there any way to assume that r < length store so that it reduces in the normalizer ? *\) *)
(* let xxx = reify (read r) store *)

let total_read_lemma (store:seq int) (r:nat)
  : Lemma (requires r < length store) (ensures Some? (fst (reify (read r) store)))
= ()

let total_write_lemma (store:seq int) (r:nat) (x:int)
  : Lemma (requires r < length store) (ensures Some? (fst (reify (write r x) store)))
= ()


let read_write_lemma1 (store:seq int) (r:nat) (x:int)
    : Lemma (requires (r < length store))
      (ensures (r < length store /\ normalize_term (fst (reify (let () = write_tot r x in read_tot r) store)) == Some x))
= ()

