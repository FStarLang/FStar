module NestedProjectors

(* Issue #4463: normalizing a deeply nested chain of *stuck* projections used to
   be quadratic in the nesting depth, because the scrutinee of every projector
   application was speculatively reduced to weak head normal form and that work
   was then thrown away as soon as the projection turned out to be stuck.  [g]
   below took tens of seconds to check; it should now take about a second. *)

noeq
type b = | B : b -> b

let rec idn (n:nat) (y:b) : Tot b (decreases n) =
  if n = 0 then y else idn (n - 1) y

let g (x:b) : b =
  FStar.Pervasives.norm [delta; iota; zeta; primops] (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (B?._0 (idn 300 (x)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(* The dual property: reducing a projection must *not* normalize the whole
   scrutinee, only the field that is selected. If it did, the [idnat 2000000]
   below would be unfolded two million times. *)

noeq
type r = | R : a:nat -> bb:nat -> r

let rec idnat (n:nat) (y:nat) : Tot nat (decreases n) =
  if n = 0 then y else idnat (n - 1) y

let mk (y:nat) : r = R y (idnat 2000000 y)

let h (x:nat) : nat = FStar.Pervasives.norm [delta; iota; zeta; primops] (R?.a (mk x))

let _ : squash (forall x. h x == x) = ()
