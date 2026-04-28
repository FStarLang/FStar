module FStar.Injection

open FStar.Fin
open FStar.Functions
module SZ = FStar.SizeT
open FStar.SizeT { (/^), (%^), (+^), (-^), ( *^ )  }
open FStar.Tactics.Easy

(* A theory of injections. As for bijections, injections are erasable
   but there is a computational variant cinj below. *)

(* total function composition *)
let o #a #b #c (g : b -> Tot c) (f : a -> Tot b) : a -> Tot c = fun x -> g (f x)
(* ghost function composition *)
let oo #a #b #c (g : b -> GTot c) (f : a -> GTot b) : a -> GTot c = fun x -> g (f x)

noeq
[@@erasable]
type injection (a b : Type) = {
  f : a -> GTot b;

  is_inj : x:a -> y:a -> f x == f y -> x == y;
}

// Not a great symbol, but F* is limited in operator support.
[@@erasable]
let ( @~> ) a b = injection a b

let mk_injection
  (#a #b : _)
  (f : a -> GTot b)
  (is_inj : (x:a -> y:a -> f x == f y -> x == y))
  : (a @~> b) =
  Mkinjection f is_inj

(* Apply an injection to a value. *)
let ( |~> ) (#a #b : Type) (x : a) (i : a `injection` b) : GTot b = i.f x

let image_of (#a #b: Type) (i: a @~> b) : Type = FStar.Functions.image_of i.f

val inverse_f (#a #b : Type) (i : a @~> b) (y : image_of i) : GTot a

val inverse_lem (#a #b : Type) (i : a @~> b) (y : image_of i)
  : Lemma (ensures i.f (inverse_f i y) == y)
          [SMTPat (inverse_f i y)]

(* An injection can be inverted, but this requires choice. *)
let inverse (#a #b : Type) (i : a @~> b) : (image_of i @~> a) = {
  f = inverse_f i;

  is_inj = easy;
}

let lem_pat (#a #b : _) (d : a @~> b) (x : a)
  : Lemma ((inverse d).f (d.f x) == x)
          [SMTPat (d.f x)]
  = d.is_inj ((inverse d).f (d.f x)) x ()

let ( <~| ) (#a #b : Type) (y : b) (i : a `injection` b{in_image i.f y}) : GTot a =
  y |~> inverse i

let inj_prod (i1 : 'a @~> 'c) (i2 : 'b @~> 'd) : ('a & 'b @~> 'c & 'd) =
{
  f = (fun (a,b) -> (i1.f a, i2.f b));
  is_inj = easy;
}

let inj_either (i1 : 'a @~> 'c) (i2 : 'b @~> 'd) : (either 'a 'b @~> either 'c 'd) =
{
  f = (function | Inl a -> Inl (i1.f a) | Inr b -> Inr (i2.f b));
  is_inj = easy;
}

let inj_comp (i1 : 'a @~> 'b) (i2 : 'b @~> 'c) : ('a @~> 'c) =
{
  f = i2.f `oo` i1.f;
  is_inj = easy;
}

(* Computationally relevant injections *)
inline_for_extraction noextract
noeq type cinj (a b: Type) = {
  inj: (a @~> b);
  cf: cf: (a -> b) { forall x. cf x == inj.f x };
}
inline_for_extraction
let (@~>>) = cinj

inline_for_extraction noextract
let cinj_comp #a #b #c (ab: a @~>> b) (bc: b @~>> c) : (a @~>> c) =
{
  inj = ab.inj `inj_comp` bc.inj;
  cf = bc.cf `o` ab.cf;
}

inline_for_extraction noextract
let cinj_either (i1 : 'a @~>> 'c) (i2 : 'b @~>> 'd) : (either 'a 'b @~>> either 'c 'd) =
{
  inj = i1.inj `inj_either` i2.inj;
  cf = (function | Inl a -> Inl (i1.cf a) | Inr b -> Inr (i2.cf b));
}

unfold inline_for_extraction noextract
let mk_cinj #a #b (f: a -> b) (#[Tactics.V2.easy_fill ()] is_inj: _) : (a @~>> b) =
{
  inj = { f; is_inj };
  cf = f;
}

inline_for_extraction noextract
let cinj_id #a : (a @~>> a) = mk_cinj id

let inj_id #a : (a @~> a) = cinj_id.inj

unfold inline_for_extraction noextract
let inj_nat_sum_f (n1 n2 : nat) : either (fin n1) (fin n2) -> fin (n1 + n2) =
  function
    | Inl i -> i
    | Inr j -> n1 + j

inline_for_extraction noextract
let cinj_nat_sum (n1 n2 : nat) : (either (fin n1) (fin n2) @~>> fin (n1 + n2)) =
  mk_cinj (inj_nat_sum_f n1 n2)

let inj_nat_sum (n1 n2 : nat) : (either (fin n1) (fin n2) @~> fin (n1 + n2)) =
  (cinj_nat_sum n1 n2).inj

val inj_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 @~> fin n2). True)
          (ensures n1 <= n2)
