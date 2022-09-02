module Demo.Deps
open FStar.Integers
module U32 = FStar.UInt32
let uint32 = U32.t
let add_does_not_overflow (x:U32.t)
                         (y:U32.t)
  = within_bounds (Unsigned W32) (U32.v x + U32.v y)
let add (x:uint32)
        (y:uint32{add_does_not_overflow x y})
    : uint32
    = x + y
let add_mod (x y:uint32)
    : uint32
    = x +% y

include FStar.Algebra.CommMonoid
include FStar.List.Tot
include C.Loops
include LowStar.Buffer
include FStar.HyperStack.ST
include FStar.HyperStack

module CM = FStar.Algebra.CommMonoid

let monoid_laws #a (m:CM.cm a) =
    (forall x y. {:pattern m.mult x y}  m.mult x y == m.mult y x) /\
    (forall x y z.{:pattern (m.mult x (m.mult y z))} m.mult x (m.mult y z) == m.mult (m.mult x y) z) /\
    (forall x.{:pattern (m.mult x m.unit)} m.mult x m.unit == x)

let elim_monoid_laws #a (m:CM.cm a)
  : Lemma ( monoid_laws m )
  = introduce forall x y. m.mult x y == m.mult y x
    with ( m.commutativity x y );

    introduce forall x y z. m.mult x (m.mult y z) == m.mult (m.mult x y) z
    with ( m.associativity x y z );

    introduce forall x. m.mult x m.unit == x
    with ( m.identity x )

let associative_commutative_operator a =
  m:CM.cm a { monoid_laws m }

module HS = FStar.HyperStack

let lbuffer ('a:Type) (l:U32.t) = b:buffer 'a { length b == U32.v l }
let contents (b:buffer 'a) (h:HS.mem) = as_seq h b
let map_contents (f: 'a -> 'b) (b:buffer 'a) (h:HS.mem) = seq_map f (contents b h)


