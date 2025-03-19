module FStarC.Class.Monoid

open FStarC
open FStarC.Effect

class monoid (a:Type) = {
   mzero : a;
   mplus : a -> a -> a;
}

(* Alias *)
val ( ++ ) (#a:Type) {| monoid a |} : a -> a -> a

val msum (#a:Type) {| monoid a |} (xs:list a) : a

instance val monoid_int : monoid int
instance val monoid_string : monoid string
instance val monoid_list (a:Type) : Tot (monoid (list a))
