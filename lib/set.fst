module Set
open Prims.PURE

(*private extensional*) type set (a:Type) = a -> Tot bool

assume type Equal : #a:Type -> set a -> set a -> Type

(* private *) assume EqualDef : (forall (a:Type) (s1:set a) (s2:set a). Equal s1 s2 <==> (forall x. s1 x = s2 x))

(* private *) assume Extensionality : (forall (a:Type) (s1:set a) (s2:set a). Equal s1 s2 <==> s1 = s2)

val empty : a:Type -> Tot (set a)
(* private *) let empty = (fun _ -> false)

val singleton : a:Type -> a -> Tot (set a)
(* private *) let singleton x = (fun y -> y = x)

val union : a:Type -> set a -> set a -> Tot (set a)
(* private *) let union s1 s2 = (fun x -> s1 x || s2 x)

val intersect : a:Type -> set a -> set a -> Tot (set a)
(* private *) let intersect s1 s2 = (fun x -> s1 x && s2 x)

val complement : a:Type -> set a -> Tot (set a)
(* private *) let complement s = (fun x -> not (s x))

val mem : a:Type -> a -> set a -> Tot bool
(* private *) let mem x s = s x

val memEmpty : a:Type -> x:a -> Lemma (requires True) (ensures (not (mem x empty))) [SMTPat (mem x empty)]
(* private *) let memEmpty (a:Type) (x:a) = ()

val memSingleton : a:Type -> x:a -> y:a -> Lemma (requires True) (ensures (mem x (singleton y) == (x = y))) [SMTPat (mem x (singleton y))]
(* private *) let memSingleton (a:Type) (x:a) (y:a) = ()

val memUnion : a:Type -> s1:set a -> s2:set a -> x:a -> Lemma (requires True) (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2))) [SMTPat (mem x (union s1 s2))]
(* private *) let memUnion (a:Type) (s1:set a) (s2:set a) (x:a) = ()

val memIntersect : a:Type -> s1:set a -> s2:set a -> x:a -> Lemma (requires True) (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2))) [SMTPat (mem x (intersect s1 s2))]
(* private *) let memIntersect (a:Type) (s1:set a) (s2:set a) (x:a) = ()

val memComplement : a:Type -> s:set a -> x:a -> Lemma (requires True) (ensures (mem x (complement s) = not (mem x s))) [SMTPat (mem x (complement s))]
(* private *) let memComplement (a:Type) (s:set a) (x:a) = ()

val extensional : a:Type -> s1:set a -> s2:set a -> Lemma (requires True) (ensures (Equal s1 s2 <==> s1 = s2)) (* error: [SMTPat (Equal a s1 s2)] *)
(* private *) let extensional (a:Type) (s1:set a) (s2:set a) = ()

val equals : a:Type -> s1:set a -> s2:set a -> Lemma (requires True) (ensures (Equal s1 s2 <==> (forall x. (* error: {:pattern (mem x s1); (mem x s2)}*) mem x s1 = mem x s2))) (* error: [SMTPat (Equal a s1 s2)] *)
(* private *) let equals (a:Type) (s1:set a) (s2:set a) = ()

let minus (a:Type) (s1:set a) (s2:set a) = intersect s1 (complement s2)

opaque type Subset' (a:Type) (s1:set a) (s2:set a) = (forall (x:a).{:pattern mem x s1} mem x s1 ==> mem x s2)

type Subset : #a:Type -> set a -> set a -> Type = fun (a:Type) (s1:set a) (s2:set a) -> Subset' a s1 s2
