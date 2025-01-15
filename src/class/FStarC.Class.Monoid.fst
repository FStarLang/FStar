module FStarC.Class.Monoid

open FStarC
open FStarC.Effect
open FStarC.List

let ( ++ ) #a {| monoid a |} = mplus #a

let msum xs = fold_left mplus mzero xs

instance monoid_int : monoid int = {
   mzero = 0;
   mplus = (fun x y -> x + y);
}

instance monoid_string : monoid string = {
   mzero = "";
   mplus = (fun x y -> x ^ y);
}

instance monoid_list (a:Type) : Tot (monoid (list a)) = {
   mzero = [];
   mplus = (fun x y -> x @ y);
}

(* Funny output from Copilot... not bad!

instance monoid_effect (a:Type) (e:effect) : monoid (a!e) = {
   mzero = return mzero;
   mplus = (fun x y -> x >>= (fun x -> y >>= (fun y -> return (mplus x y))));
}

*)
