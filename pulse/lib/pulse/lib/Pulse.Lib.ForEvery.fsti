module Pulse.Lib.ForEvery 

#lang-pulse
open Pulse
open FStar.Fin
open FStar.Bijection
open FStar.Enumerable
open Pulse.Lib.Trade

// FIXME: remove and use Prims t2b
let t2b =
  FStar.IndefiniteDescription.strong_excluded_middle

val ( forall+ )
  (#a:Type)
  (f : a -> slprop)
  : slprop

val timeless_forevery #a (p: a -> slprop) :
  Lemma (requires forall x. timeless (p x))
    (ensures timeless (op_forall_Plus p))
    [SMTPat (timeless (op_forall_Plus p))]

unfold
let forevery
  (a:Type)
  (f : a -> slprop)
  : slprop
  = op_forall_Plus #a f

ghost
fn forevery_ext
  (#a:Type0)
  (f : a -> slprop)
  (g : a -> slprop { forall x. f x == g x })
  requires
    forall+ (x:a). f x
  ensures
    forall+ (x:a). g x

ghost
fn forevery_intro_pure (#a:Type0) (p: a -> prop)
  requires
    pure (forall x. p x)
  ensures
    forall+ x. pure (p x)

ghost
fn forevery_intro_pure_2 (#a:Type0) (#b:Type0) (p: a -> b -> prop)
  requires
    pure (forall x y. p x y)
  ensures
    forall+ (x:a) (y:b). pure (p x y)

ghost
fn forevery_intro_empty (#a:Type0) (p: a -> slprop)
  requires
    pure (forall (x:a). False)
  ensures
    forall+ (x:a). p x

ghost
fn forevery_elim_empty (#a:Type0) (p: a -> slprop)
  requires
    pure (forall (x:a). False)
  requires
    forall+ (x:a). p x

ghost
fn forevery_intro_false (#a:Type0) (p: a -> slprop)
  ensures
    forall+ (x:a {False}). p x

ghost
fn forevery_intro_fill (#a: Type0) (p: a -> slprop)
  (f: (x:a -> stt_ghost unit emp_inames emp (fun _ -> p x)))
  ensures
    forall+ x. p x

ghost
fn forevery_insert
  (#a: Type0)
  (#f: a->prop)
  (p: a -> slprop)
  (y: a)
  requires
    forall+ (x:a {f x}). p x
  requires
    p y
  requires
    pure (~(f y))
  ensures
    forall+ (x:a {f x \/ y == x}). p x

ghost
fn forevery_remove'
  (#a: Type0)
  (f: a->prop)
  (p: a -> slprop)
  (y: a { f y })
  requires
    forall+ (x:a {f x}). p x
  ensures
    forall+ (x:a {f x /\ x =!= y}). p x
  ensures
    p y

ghost
fn forevery_remove
  (#a: Type0)
  (p: a -> slprop)
  (y: a)
  requires
    forall+ (x:a). p x
  ensures
    forall+ (x:a {x =!= y}). p x
  ensures
    p y

ghost
fn forevery_fill
  (#a: Type0)
  (#f: a->prop)
  (p: a -> slprop)
  (pred: a -> prop)
  (g: (x:a{pred x} -> stt_ghost unit emp_inames emp (fun _ -> p x)))
  requires
    forall+ (x:a {f x}). p x
  requires
    pure (forall x. pred x ==> ~(f x))
  ensures
    forall+ (x:a {f x \/ pred x}). p x

ghost
fn forevery_refine_ext'
  (#a: Type0)
  (#f g: a->prop)
  (#_ : squash (forall x. f x <==> g x))
  (p: (x:a{f x} -> slprop))
  requires
    forall+ (x:a {f x}). p x
  ensures
    forall+ (w:a {g w}). p w

ghost
fn forevery_refine_ext
  (#a: Type0)
  (#f g: a->prop)
  (p: a -> slprop)
  requires
    forall+ (x:a {f x}). p x
  requires
    pure (forall x. f x <==> g x)
  ensures
    forall+ (w:a {g w}). p w

ghost
fn forevery_unrefine
  (#a: Type0)
  (#f: a->prop)
  (p: a -> slprop)
  requires
    forall+ (x:a {f x}). p x
  requires
    pure (forall x. f x)
  ensures
    forall+ x. p x

ghost
fn forevery_refine_split
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  requires
    forall+ x. p x
  ensures
    forall+ (x:a{f x}). p x
  ensures
    forall+ (x:a{~(f x)}). p x

ghost
fn forevery_refine_join
  (#a:Type0)
  (p: a -> slprop)
  (f g: a -> prop)
  requires
    forall+ (x:a{f x}). p x
  requires
    forall+ (x:a{g x}). p x
  requires
    pure (forall x. ~(f x /\ g x))
  ensures
    forall+ (x:a{f x \/ g x}). p x

(* Like forevery_refine_join, but accepts a payload that is only defined
   on the union of the two ranges. The output predicate h must be
   equivalent to (f x \/ g x). *)
ghost
fn forevery_refine_join'
  (#a:Type0)
  (f g: a -> prop)
  (p: (x:a{f x \/ g x}) -> slprop)
  requires
    forall+ (x:a{f x}). p x
  requires
    forall+ (x:a{g x}). p x
  requires
    pure (forall x. ~(f x /\ g x))
  ensures
    forall+ (x:a{f x \/ g x}). p x

let unless (p: prop) (q: slprop) : slprop =
  if t2b p then emp else q

let when_ (p: prop) (q: slprop) : slprop =
  if t2b p then q else emp

(* Needed for when the rhs is partially defined *)
let when__ (p: prop) (q: squash p -> slprop) : slprop =
  if t2b p then q () else emp

ghost
fn forevery_unrefine_pred
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  requires
    forall+ (x:a { f x }). p x
  ensures
    forall+ (x:a). when_ (f x) (p x)

ghost
fn forevery_unrefine_pred'
  (#a:Type0)
  (f: a -> prop)
  (p: (x:a -> squash (f x) -> slprop))
  requires
    forall+ (x:a { f x }). p x ()
  ensures
    forall+ (x:a). when__ (f x) (p x)

ghost
fn forevery_refine_pred
  (#a:Type0)
  (p: a -> slprop)
  (f: a -> prop)
  requires
    forall+ (x:a). when_ (f x) (p x)
  ensures
    forall+ (x:a { f x }). p x

ghost
fn forevery_ext_2
  (#a:Type0)
  (#b:Type0)
  (f : a -> b -> slprop)
  (g : a -> b -> slprop)
  requires
    pure (forall x y. f x y == g x y)
  requires
    forall+ (x:a) (y:b). f x y
  ensures
    forall+ (x:a) (y:b). g x y

ghost
fn forevery_flatten
  (#a:Type0)
  (#b:Type0)
  (f : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). f x y
  ensures
    forall+ (xy : a & b). f xy._1 xy._2

ghost
fn forevery_flatten_dep
  (#a : Type0)
  (#b : a -> Type0)
  (f : (x:a -> b x -> slprop))
  requires
    forall+ (x:a) (y:b x). f x y
  ensures
    forall+ (xy : (x:a & b x)). f xy._1 xy._2

ghost
fn forevery_flatten'
  (#a:Type0)
  (#b:Type0)
  (f : a & b -> slprop)
  requires
    forall+ (x:a) (y:b). f (x, y)
  ensures
    forall+ (xy : a & b). f xy

ghost
fn forevery_unflatten
  (#a:Type0)
  (#b:Type0)
  (f : a -> b -> slprop)
  requires
    forall+ (xy : a & b). f xy._1 xy._2
  ensures
    forall+ (x:a) (y:b). f x y

ghost
fn forevery_unflatten'
  (#a:Type0)
  (#b:Type0)
  (f : a & b -> slprop)
  requires
    forall+ (xy : a & b). f xy
  ensures
    forall+ (x:a) (y:b). f (x, y)

ghost
fn forevery_unflatten_dep
  (#a : Type0)
  (#b : a -> Type0)
  (f : (x:a -> b x -> slprop))
  requires
    forall+ (xy : (x:a & b x)). f xy._1 xy._2
  ensures
    forall+ (x:a) (y:b x). f x y

ghost
fn forevery_unflatten_dep'
  (#a : Type0)
  (#b : a -> Type0)
  (f : (x:a & b x) -> slprop)
  requires
    forall+ (xy : (x:a & b x)). f xy
  ensures
    forall+ (x:a) (y:b x). f (|x, y|)

ghost
fn forevery_commute
  (#a:Type0)
  (#b:Type0)
  (f : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). f x y
  ensures
    forall+ (y:b) (x:a). f x y

ghost
fn forevery_iso
  (#a:Type0)
  (#b:Type0)
  (bij : a =~ b)
  (p : a -> slprop)
  requires
    forall+ (x:a). p x
  ensures
    forall+ (y:b). p (bij.left y)

ghost
fn forevery_iso_back
  (#a:Type0)
  (#b:Type0)
  (bij : a =~ b)
  (p : a -> slprop)
  requires
    forall+ (y:b). p (bij.left y)
  ensures
    forall+ (x:a). p x

// FIXME: without this, Pulse will not type-check calls to forevery_fin_{extend,restrict}
let fin_coerce #m #n (i: fin n { i < m }) : fin m = i

ghost
fn forevery_fin_extend
  (#n: nat)
  (m: nat { m >= n })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin n). p i
  ensures
    forall+ (i: fin m { i < n }). p (fin_coerce i)

ghost
fn forevery_fin_restrict
  (#n: nat)
  (m: nat { m >= n })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin m { i < n }). p (fin_coerce i)
  ensures
    forall+ (i: fin n). p i

ghost
fn forevery_fin_pop
  (n: nat { n > 0 })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin n). p i
  ensures
    forall+ (i: fin (n-1)). p (fin_coerce i)
  ensures
    p (n-1)

ghost
fn forevery_fin_push
  (n: nat { n > 0 })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin (n-1)). p (fin_coerce i)
  requires
    p (n-1)
  ensures
    forall+ (i: fin n). p i

ghost
fn forevery_fin_pop_shift
  (n: nat { n > 0 })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin n). p i
  ensures
    forall+ (i: fin (n-1)). p (i + 1)
  ensures
    p 0

ghost
fn forevery_fin_push_shift
  (n: nat { n > 0 })
  (p: fin n -> slprop)
  requires
    forall+ (i: fin (n-1)). p (i + 1)
  requires
    p 0
  ensures
    forall+ (i: fin n). p i

ghost
fn forevery_exists
  (#a: Type0) {| enumerable a |}
  (#b: Type0)
  (p: a -> b -> slprop)
  requires
    forall+ (x:a). exists* (y:b). p x y
  returns
    y:(a->GTot b)
  ensures
    forall+ (x:a). p x (y x)

ghost
fn forevery_exists_2
  (#a: Type0) {| enumerable a |}
  (#b: Type0) {| enumerable b |}
  (#c: Type0)
  (p: a -> b -> c -> slprop)
  requires
    forall+ (x:a) (y:b).
      exists* (z:c). p x y z
  returns
    f:(a->b->GTot c)
  ensures
    forall+ (x:a) (y:b).
       p x y (f x y)

ghost
fn forevery_emp_intro
  (a : Type0)
  requires
    emp
  ensures
    forall+ (_ : a). emp

ghost
fn forevery_emp_elim
  (a : Type0)
  requires
    forall+ (_ : a). emp
  ensures
    emp

ghost
fn forevery_unit_intro
  (p : slprop)
  requires
    p
  ensures
    forall+ (_:unit). p

ghost
fn forevery_unit_elim
  (p : slprop)
  requires
    forall+ (_:unit). p
  ensures
    p

ghost
fn forevery_bool_intro
  (p: bool -> slprop)
  requires
    p false
  requires
    p true
  ensures
    forall+ (x: bool). p x

ghost
fn forevery_bool_elim
  (p: bool -> slprop)
  requires
    forall+ (x: bool). p x
  ensures
    p false
  ensures
    p true

ghost
fn forevery_singleton_intro'
  (#a:Type0)
  (p : a -> slprop)
  (x: a)
  requires
    pure (forall (y: a). x == y)
  requires
    p x
  ensures
    forall+ (x:a). p x

ghost
fn forevery_singleton_elim'
  (#a:Type0)
  (p : a -> slprop)
  (x: a)
  requires
    pure (forall (y: a). x == y)
  requires
    forall+ (x:a). p x
  ensures
    p x

ghost
fn forevery_singleton_intro
  (#a:Type0) {| enumerable a |}
  (p : a -> slprop { cardinal a #_ == 1 })
  requires
    p (of_nat 0)
  ensures
    forall+ (x:a). p x

ghost
fn forevery_singleton_elim
  (#a:Type0) {| enumerable a |}
  (p : a -> slprop { cardinal a #_ == 1 })
  requires
    forall+ (x:a). p x
  ensures
    p (of_nat 0)

(* SHOULD NOT BE NEEDED!
   1) We should mark the p argument of forevery as extensional,
      and have the checker do the work for us.
   2) Using forall+, everything should be uniformly eta-expanded.
 *)
ghost
fn forevery_eta
  (#a:Type0)
  (p : a -> slprop)
  requires
    forevery a p
  ensures
    forevery a (fun x -> p x)

ghost
fn forevery_uneta
  (#a:Type0)
  (p : a -> slprop)
  requires
    forevery a (fun x -> p x)
  ensures
    forevery a p

ghost
fn forevery_rw_type
  (a:Type0)
  (b:Type{a == b})
  (f : a -> slprop)
  requires
    forall+ (x:a). f x
  ensures
    forall+ (x:b). f x

ghost
fn forevery_rw_size
  (n1 : nat)
  (n2 : nat{n1 == n2})
  (#p : fin n1 -> slprop)
  requires
    forall+ (i : fin n1). p i
  ensures
    forall+ (i : fin n2). p i

ghost
fn forevery_rw_size2
  (n1 : nat)
  (n2 : nat{n1 == n2})
  (n3 : nat)
  (n4 : nat{n3 == n4})
  (#p : fin n1 -> fin n3 -> slprop)
  requires
    forall+ (i : fin n1) (j : fin n3). p i j
  ensures
    forall+ (i : fin n2) (j : fin n4). p i j

ghost
fn forevery_factor
  (n : nat)
  (d1 : nat) (d2 : nat { n == d1 * d2 })
  (p : fin n -> slprop)
  requires
    forall+ (i:fin n). p i
  ensures
    forall+ (i1:fin d1) (i2:fin d2). p (i1 * d2 + i2)

ghost
fn forevery_factor'
  (n : nat)
  (d1 : nat) (d2 : nat { n == d1 * d2 })
  (p : fin d1 -> fin d2 -> slprop)
  requires
    forall+ (i:fin n). p (i/d2) (i%d2)
  ensures
    forall+ (i1:fin d1) (i2:fin d2). p i1 i2

ghost
fn forevery_unfactor
  (n : nat)
  (d1 : nat) (d2 : nat { n == d1 * d2 })
  (p : fin n -> slprop)
  requires
    forall+ (i1:fin d1) (i2:fin d2). p (i1 * d2 + i2)
  ensures
    forall+ (i:fin n). p i

ghost
fn forevery_unfactor'
  (n : nat)
  (d1 : nat) (d2 : nat { n == d1 * d2 })
  (p : fin d1 -> fin d2 -> slprop)
  requires
    forall+ (i1:fin d1) (i2:fin d2). p i1 i2
  ensures
    forall+ (i:fin n). p (i/d2) (i%d2)

ghost
fn forevery_zip
  (#a:Type0)
  (p1 p2 : a -> slprop)
  requires
    (forall+ (x:a). p1 x) **
    (forall+ (x:a). p2 x)
  ensures
    forall+ (x:a). p1 x ** p2 x

ghost
fn forevery_unzip
  (#a:Type0)
  (p1 p2 : a -> slprop)
  requires
    forall+ (x:a). p1 x ** p2 x
  ensures
    (forall+ (x:a). p1 x) **
    (forall+ (x:a). p2 x)

ghost
fn forevery_zip3
  (#a:Type0)
  (p1 p2 p3 : a -> slprop)
  requires
    forall+ (x:a). p1 x
  requires
    forall+ (x:a). p2 x
  requires
    forall+ (x:a). p3 x
  ensures
    forall+ (x:a). p1 x ** p2 x ** p3 x

ghost
fn forevery_unzip3
  (#a:Type0)
  (p1 p2 p3 : a -> slprop)
  requires
    forall+ (x:a). p1 x ** p2 x ** p3 x
  ensures
    forall+ (x:a). p1 x
  ensures
    forall+ (x:a). p2 x
  ensures
    forall+ (x:a). p3 x

ghost
fn forevery_map
  (#a:Type0)
  (p1 p2 : a -> slprop)
  (f : (x:a -> stt_ghost unit emp_inames (p1 x) (fun _ -> p2 x)))
  requires
    forall+ (x:a). p1 x
  ensures
    forall+ (x:a). p2 x

ghost
fn forevery_map_2
  (#a:Type0)
  (#b:Type0)
  (p1 p2 : a -> b -> slprop)
  (f : (x:a -> y:b -> stt_ghost unit emp_inames (p1 x y) (fun _ -> p2 x y)))
  requires
    forall+ (x:a) (y:b). p1 x y
  ensures
    forall+ (x:a) (y:b). p2 x y

ghost
fn forevery_map'
  (#a:Type0)
  (#b:Type0 { a == b })
  (p1 : a -> slprop)
  (p2 : b -> slprop)
  (f : (x:a -> y:b { x === y } -> stt_ghost unit emp_inames (p1 x) (fun _ -> p2 y)))
  requires
    forall+ (x:a). p1 x
  ensures
    forall+ (x:b). p2 x

ghost
fn forevery_zip_2
  (#a:Type0)
  (#b:Type0)
  (p1 p2 : a -> b -> slprop)
  requires
    (forall+ (x:a) (y:b). p1 x y) **
    (forall+ (x:a) (y:b). p2 x y)
  ensures
    forall+ (x:a) (y:b). p1 x y ** p2 x y

ghost
fn forevery_unzip_2
  (#a:Type0)
  (#b:Type0)
  (p1 p2 : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). p1 x y ** p2 x y
  ensures
    (forall+ (x:a) (y:b). p1 x y) **
    (forall+ (x:a) (y:b). p2 x y)

unfold
let pad_f (#n1 : nat) (n2 : nat{n1 <= n2})
  (f : fin n1 -> slprop)
  : fin n2 -> slprop =
  fun i ->
    if i < n1 then f i else emp

ghost
fn forevery_pad
  (n1 : nat)
  (n2 : nat{n1 <= n2})
  (p : fin n1 -> slprop)
  requires
    forall+ (i : fin n1). p i
  ensures
    forall+ (i : fin n2). pad_f n2 p i


ghost
fn forevery_unpad
  (n1 : nat)
  (n2 : nat{n1 <= n2})
  (p : fin n1 -> slprop)
  requires
    forall+ (i : fin n2). pad_f n2 p i
  ensures
    forall+ (i : fin n1). p i

ghost
fn forevery_extract
  (#a:Type0)
  (z : a)
  (p : a -> slprop)
  requires
    forall+ (x:a). p x
  ensures
    p z ** (p z @==> forall+ (x:a). p x)

ghost
fn forevery_extract'
  (#a:Type0)
  (z : a)
  (p  : a -> slprop)
  requires
    forall+ (x:a). p x
  ensures
    p z **
      (forall* (p' : a -> slprop).
        p' z ** pure (forall (x:a{x =!= z}). p' x == p x)
          @==> (forall+ (x:a). p' x))

ghost
fn forevery_extract_2
  (#a:Type0)
  (#b:Type0)
  (z : a) (w : b)
  (p : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). p x y
  ensures
    p z w ** (p z w @==> forall+ (x:a) (y:b). p x y)

ghost
fn forevery_extract_if
  (#a:Type0)
  (z : a)
  (p : a -> slprop)
  requires
    forall+ (x:a). p x
  ensures
    p z **
    (forall+ (x:a).
      if t2b (x == z) then emp else p x)

ghost
fn forevery_unextract_if
  (#a:Type0)
  (z : a)
  (p : a -> slprop)
  requires
    p z **
    (forall+ (x:a).
      if t2b (x == z) then emp else p x)
  ensures
    forall+ (x:a). p x

ghost
fn forevery_extract_if_eqtype
  (#a:eqtype)
  (z : a)
  (p : a -> slprop)
  requires
    forall+ (x:a). p x
  ensures
    p z **
    (forall+ (x:a).
      if x = z then emp else p x)

ghost
fn forevery_unextract_if_eqtype
  (#a:eqtype)
  (z : a)
  (p : a -> slprop)
  requires
    p z **
    (forall+ (x:a).
      if x = z then emp else p x)
  ensures
    forall+ (x:a). p x

ghost
fn forevery_extract_if_2
  (#a:Type0)
  (#b:Type0)
  (z : a) (w : b)
  (p : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). p x y
  ensures
    p z w **
    (forall+ (x:a) (y:b).
      if t2b ((x,y) == (z,w)) then emp else p x y)


ghost
fn forevery_intro_if
  (#a:Type0)
  (z : a)
  (p : a -> slprop)
  requires
    p z
  ensures
    (forall+ (x:a).
      if t2b (x == z) then p x else emp)

ghost
fn forevery_split_either
  (#a #b : Type0)
  (p : either a b -> slprop)
  requires
    forall+ (x:either a b). p x
  ensures
    (forall+ (x:a). p (Inl x)) **
    (forall+ (x:b). p (Inr x))

ghost
fn forevery_join_either
  (#a #b : Type0)
  (p : either a b -> slprop)
  requires
    (forall+ (x:a). p (Inl x)) **
    (forall+ (x:b). p (Inr x))
  ensures
    forall+ (x:either a b). p x

ghost
fn forevery_map_extra
  (#a:Type0) {| enumerable a |}
  (k : slprop)
  (p1 p2 : a -> slprop)
  (f : (x:a -> stt_ghost unit emp_inames (k ** p1 x) (fun _ -> k ** p2 x)))
  preserves k
  requires
    forall+ (x:a). p1 x
  ensures
    forall+ (x:a). p2 x

ghost
fn forevery_flatten3'
  (#a #b #c : Type0)
  (f : a & b & c -> slprop)
  requires
    forall+ (x:a) (y:b) (z:c). f (x, y, z)
  ensures
    forall+ (xyz : a & b & c). f xyz

ghost
fn forevery_unflatten3'
  (#a #b #c : Type0)
  (f : a & b & c -> slprop)
  requires
    forall+ (xyz : a & b & c). f xyz
  ensures
    forall+ (x:a) (y:b) (z:c). f (x, y, z)

ghost
fn forevery_flatten4'
  (#a #b #c #d : Type0)
  (f : a & b & c & d -> slprop)
  requires
    forall+ (x:a) (y:b) (z:c) (w:d). f (x, y, z, w)
  ensures
    forall+ (xyzw : a & b & c & d). f xyzw

ghost
fn forevery_unflatten4'
  (#a #b #c #d : Type0)
  (f : a & b & c & d -> slprop)
  requires
    forall+ (xyzw : a & b & c & d). f xyzw
  ensures
    forall+ (x:a) (y:b) (z:c) (w:d). f (x, y, z, w)



ghost
fn forevery_split_or_2
  (#a:Type0)
  (r s : a -> prop)
  (p : a -> slprop)
  requires
    pure (~ (exists (x:a). r x /\ s x))
  requires
    forall+ (x:a { r x \/ s x }). p x
  ensures
    (forall+ (x:a { r x }). p x) **
    (forall+ (x:a { s x }). p x)

ghost
fn forevery_split_or_n
  (#a #b:Type0)
  (r : b -> a -> prop)
  (p : a -> slprop)
  requires
    pure (forall (i1 i2 : b) x.
      r i1 x /\ r i2 x ==> i1 == i2)
  requires
    forall+ (x:a {exists i. r i x}). p x
  ensures
    forall+ (i : b).
      forall+ (x:a { r i x }).
        p x

ghost
fn forevery_join_or_n
  (#a #b:Type0)
  (r : b -> a -> prop)
  (p : a -> slprop)
  requires
    pure (forall (i1 i2 : b) x.
      r i1 x /\ r i2 x ==> i1 == i2)
  requires
    forall+ (i : b).
      forall+ (x:a { r i x }).
        p x
  ensures
    forall+ (x:a {exists i. r i x}). p x

ghost
fn on_forevery_elim (#a: Type0) (p: a -> slprop) (l: loc_id)
  requires
    on l (forall+ (x:a). p x)
  ensures
    forall+ (x:a). on l (p x)

instance val is_send_across_forevery
  (#a:Type u#0) (#b:Type) (p: a -> slprop) (vis:loc_id -> b) {| (x:a -> is_send_across vis (p x)) |} :
  is_send_across vis (forall+ x. p x)

instance is_send_forevery
  (#a:Type u#0) (p: a -> slprop) {| sa: (x:a -> is_send (p x)) |} :
  is_send (forall+ x. p x)
  = is_send_across_forevery p _ #sa

instance placeless_forevery
  (#a:Type u#0) (p: a -> slprop) {| sa: (x:a -> placeless (p x)) |} :
  placeless (forall+ x. p x)
  = is_send_across_forevery p _ #sa

ghost
fn forevery_factor_2
  (m : nat) (m1 m2 : nat { m == m1 * m2 })
  (n : nat) (n1 n2 : nat { n == n1 * n2 })
  (p : fin m -> fin n -> slprop)
  requires
    forall+ (i : fin m) (j : fin n). p i j
  ensures
    forall+ (i1 : fin m1) (i2 : fin m2) (j1 : fin n1) (j2 : fin n2).
      p (i1 * m2 + i2) (j1 * n2 + j2)

ghost
fn forevery_unfactor_2
  (m : nat) (m1 m2 : nat { m == m1 * m2 })
  (n : nat) (n1 n2 : nat { n == n1 * n2 })
  (p : fin m -> fin n -> slprop)
  requires
    forall+ (i1 : fin m1) (i2 : fin m2) (j1 : fin n1) (j2 : fin n2).
      p (i1 * m2 + i2) (j1 * n2 + j2)
  ensures
    forall+ (i : fin m) (j : fin n). p i j

ghost
fn forevery_mid_flip
  (#a #b #c : Type0)
  (p : a -> b -> c -> slprop)
  requires
    forall+ (x:a) (y:b) (z:c). p x y z
  ensures
    forall+ (x:a) (z:c) (y:b). p x y z

ghost
fn forevery_extract_pure
  (#a:Type0) {| enumerable a |}
  (p : a -> slprop)
  (q : a -> prop)
  (f : (x:a) -> stt_ghost unit emp_inames (p x) (fun _ -> p x ** pure (q x)))
  preserves
    forall+ (x:a). p x
  ensures
    pure (forall (x:a). q x)

ghost
fn forevery_extract_pure_2
  (#a #b : Type0)
  {| enumerable a, enumerable b |}
  (p : a -> b -> slprop)
  (q : a -> b -> prop)
  (f : (x:a) -> (y:b) ->
    stt_ghost unit emp_inames (p x y) (fun _ -> p x y ** pure (q x y)))
  preserves
    forall+ (x:a) (y:b). p x y
  ensures
    pure (forall (x:a) (y:b). q x y)

ghost
fn forevery_rw_size4
  (n1 : nat)
  (n2 : nat{n1 == n2})
  (n3 : nat)
  (n4 : nat{n3 == n4})
  (n5 : nat)
  (n6 : nat{n5 == n6})
  (n7 : nat)
  (n8 : nat{n7 == n8})
  (#p : fin n1 -> fin n3 -> fin n5 -> fin n7 -> slprop)
  requires
    forall+ (i : fin n1) (j : fin n3) (k : fin n5) (l : fin n7). p i j k l
  ensures
    forall+ (i : fin n2) (j : fin n4) (k : fin n6) (l : fin n8). p i j k l

(* === New combinators for 4-way quantifiers === *)

(* Swap middle two quantifiers in a 4-nested quantifier:
   forall+ a b c d. P a b c d  -->  forall+ a c b d. P a b c d *)
ghost
fn forevery_swap_mid_4
  (#a #b #c #d : Type0)
  (p : a -> b -> c -> d -> slprop)
  requires
    forall+ (w:a) (x:b) (y:c) (z:d). p w x y z
  ensures
    forall+ (w:a) (y:c) (x:b) (z:d). p w x y z

(* 3-way zip for 2-argument predicates *)
ghost
fn forevery_zip3_2
  (#a #b : Type0)
  (p1 p2 p3 : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). p1 x y
  requires
    forall+ (x:a) (y:b). p2 x y
  requires
    forall+ (x:a) (y:b). p3 x y
  ensures
    forall+ (x:a) (y:b). p1 x y ** p2 x y ** p3 x y

(* 4-way zip for 2-argument predicates *)
ghost
fn forevery_zip4_2
  (#a #b : Type0)
  (p1 p2 p3 p4 : a -> b -> slprop)
  requires
    forall+ (x:a) (y:b). p1 x y
  requires
    forall+ (x:a) (y:b). p2 x y
  requires
    forall+ (x:a) (y:b). p3 x y
  requires
    forall+ (x:a) (y:b). p4 x y
  ensures
    forall+ (x:a) (y:b). p1 x y ** p2 x y ** p3 x y ** p4 x y

(* Extensionality for 4-argument predicates *)
ghost
fn forevery_ext_4
  (#a #b #c #d : Type0)
  (f : a -> b -> c -> d -> slprop)
  (g : a -> b -> c -> d -> slprop { forall w x y z. f w x y z == g w x y z })
  requires
    forall+ (w:a) (x:b) (y:c) (z:d). f w x y z
  ensures
    forall+ (w:a) (x:b) (y:c) (z:d). g w x y z

ghost
fn forevery_push_pure
  (#a:Type0) (p : a -> slprop)
  (q : prop)
  requires
    pure q ** (forall+ (x:a). p x)
  ensures
    forall+ (x:a). p x ** pure q
