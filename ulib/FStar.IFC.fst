module FStar.IFC
(**
 * FStar.IFC provides a simple, generic abstraction
 * for monadic information-flow control
 * based on a user-defined (semi-)lattice of information flow labels
 **)

(* Basic definitions for a join semilattice *)
let associative #a (f: (a -> a -> a)) =
  forall x y z. f (f x y) z == f x (f y z)

let commutative #a (f: (a -> a -> a)) =
  forall x y. f x y == f y x

let idempotent #a (f: (a -> a -> a)) =
  forall x. f x x == x

noeq
type semi_lattice (a:Type) = {
  top: a;
  lub: (f: (a -> a -> a) {
    associative f /\
    commutative f /\
    idempotent f
 })
}

(* A lattice element is just an element of the carrier type *)
let lattice_element (#a:Type) (s:semi_lattice a) = a

(* A convenience for joining elements in the lattice *)
unfold
let lub #a #l (x:lattice_element #a l) (y:lattice_element #a l)
  : lattice_element l
  = l.lub x y

////////////////////////////////////////////////////////////////////////////////

/// The main type provided by this module is `protected l b`
/// i.e., a `b`-typed value protected at IFC level `l`
abstract
let protected (#a:Type)
              (#sl:semi_lattice a)
              (l:lattice_element sl)
              (b:Type) = b

/// At the specification level a `protected l b` is just a `b`
abstract
let reveal #a #sl (#l:lattice_element #a sl)
           #b (x:protected l b)
   : GTot b
   = x

/// And any `b` can be promoted to a `protected l b`
/// i.e., `protected l b` is only meant to enforce confidentiality
abstract
let hide #a (#l:semi_lattice a) (#tag:lattice_element l) #b (x:b)
  : Tot (protected tag b)
  = x

/// The next pair of lemmas show that reveal/hide are inverses
let reveal_hide #a #l #t #b (x:b)
  : Lemma (reveal (hide #a #l #t x) == x)
          [SMTPat (hide #a #l #t x)]
  = ()

let hide_reveal #a (#sl:semi_lattice a) (#l:lattice_element sl) #b
                (x:protected l b)
  : Lemma (hide (reveal x) == x)
          [SMTPat (reveal x)]
  = ()

/// `protected l b` is a form of parameterized monad
///  It provides:
///    -- `return` (via `hide)
///    -- `map` (i.e., it's a functor)
///    -- `join`   (so it's also a monad)
///  Which we package up as a `bind`
unfold
let return #c (#sl:semi_lattice c) #a
           (l:lattice_element sl) (x:a)
    : protected l a
    = hide x

/// This is just a map of `f` over `x`
/// But, notice the order of arguments is flipped
/// We write `map x f` instead of `map f x` so that
/// `f`'s type can depend on `x`
abstract
let map #a #b #c
        (#sl:semi_lattice c)
        (#l:lattice_element sl)
        (x:protected l a)
        (f: (y:a{y == reveal x} -> b))
    : Tot (y:protected l b{reveal y == f (reveal x)})
    = f x

/// This is almost a regular monadic `join`
/// Except notice that the label of the result is the lub
/// of the both the labels in the argument
abstract
let join #c
         (#sl:semi_lattice c)
         (#l1:lattice_element sl)
         (#l2:lattice_element sl)
         #a
         (x:protected l1 (protected l2 a))
    : Tot (y:protected (l1 `lub` l2) a {reveal y == reveal (reveal x)})
    = let y : a = x in
      y

/// This is almost like a regular bind, except
/// like `map` the type of the continuation's argument
/// depends on the argument `x`;
/// and, like `join`, the indexes on the result are at least
/// as high as the indexes of the argument
///
/// As such, any computation that observes the protected value held in
/// `x` has a secrecy level at least as secret as `x` itself
unfold
let bind #c
         (#sl:semi_lattice c)
         (#l1:lattice_element sl)
         #a
         (x:protected l1 a)
         (#l2:lattice_element sl)
         #b
         (f: (y:a{y == reveal x} -> protected l2 b))
    : Tot (protected (l1 `lub` l2) b)
    = join (map x f)
