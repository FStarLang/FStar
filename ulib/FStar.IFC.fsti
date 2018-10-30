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
type semi_lattice =
  | SemiLattice: #carrier:Type
               -> top:carrier
               -> lub:(f: (carrier -> carrier -> carrier) {
                          associative f /\
                          commutative f /\
                          idempotent f
                      })
               -> semi_lattice

let sl = FStar.Ghost.erased semi_lattice

(* A lattice element is just an element of the carrier type *)
let lattice_element (sl:sl) = Ghost.erased (SemiLattice?.carrier (Ghost.reveal sl))

(* A convenience for joining elements in the lattice *)
unfold
let lub #sl (x:lattice_element sl) (y:lattice_element sl)
  : Tot (lattice_element sl)
  = Ghost.hide (SemiLattice?.lub (Ghost.reveal sl) (Ghost.reveal x) (Ghost.reveal y))

////////////////////////////////////////////////////////////////////////////////

/// The main type provided by this module is `protected l b`
/// i.e., a `b`-typed value protected at IFC level `l`
val protected (#sl:sl)
              (l:lattice_element sl)
              (b:Type0) : Type0

/// At the specification level a `protected l b` is just a `b`
val reveal (#sl:sl) (#l:lattice_element sl)
           (#b:Type) (x:protected l b)
   : GTot b

/// And any `b` can be promoted to a `protected l b`
/// i.e., `protected l b` is only meant to enforce confidentiality
val hide (#sl:sl) (#l:lattice_element sl) (#b:Type) (x:b)
  : Tot (protected l b)

/// The next pair of lemmas show that reveal/hide are inverses
val reveal_hide (#l:sl) (#t:lattice_element l) (#b:Type) (x:b)
  : Lemma (reveal (hide #l #t x) == x)
          [SMTPat (hide #l #t x)]

val hide_reveal (#sl:sl) (#l:lattice_element sl) (#b:Type)
                (x:protected l b)
  : Lemma (hide (reveal x) == x)
          [SMTPat (reveal x)]

/// `protected l b` is a form of parameterized monad
///  It provides:
///    -- `return` (via `hide)
///    -- `map` (i.e., it's a functor)
///    -- `join`   (so it's also a monad)
///  Which we package up as a `bind`
unfold
let return #sl #a
           (l:lattice_element sl) (x:a)
    : protected l a
    = hide x

/// This is just a map of `f` over `x`
/// But, notice the order of arguments is flipped
/// We write `map x f` instead of `map f x` so that
/// `f`'s type can depend on `x`
val map (#a #b:Type)
        (#sl:sl)
        (#l:lattice_element sl)
        (x:protected l a)
        (f: (y:a{y == reveal x} -> b))
    : Tot (y:protected l b{reveal y == f (reveal x)})

/// This is almost a regular monadic `join`
/// Except notice that the label of the result is the lub
/// of the both the labels in the argument
val join (#sl:sl)
         (#l1:lattice_element sl)
         (#l2:lattice_element sl)
         (#a:Type)
         (x:protected l1 (protected l2 a))
    : Tot (y:protected (l1 `lub` l2) a {reveal y == reveal (reveal x)})

/// This is almost like a regular bind, except
/// like `map` the type of the continuation's argument
/// depends on the argument `x`;
/// and, like `join`, the indexes on the result are at least
/// as high as the indexes of the argument
///
/// As such, any computation that observes the protected value held in
/// `x` has a secrecy level at least as secret as `x` itself
unfold
let bind #sl
         (#l1:lattice_element sl)
         #a
         (x:protected l1 a)
         (#l2:lattice_element sl)
         #b
         (f: (y:a{y == reveal x} -> protected l2 b))
    : Tot (protected (l1 `lub` l2) b)
    = join (map x f)
