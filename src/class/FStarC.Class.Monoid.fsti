module FStarC.Class.Monoid

open FStarC
open FStarC.Effect

class monoid (a:Type) = {
   mzero : a;
   mplus : a -> a -> ML a;
}

(* Alias *)
val ( ++ ) (#a:Type) {| monoid a |} : a -> a -> ML a

val msum (#a:Type) {| monoid a |} (xs:list a) : ML a

instance val monoid_int : monoid int
instance val monoid_string : monoid string
instance val monoid_list (a:Type) : Tot (monoid (list a))
