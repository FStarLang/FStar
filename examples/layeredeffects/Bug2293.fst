module Bug2293

open ND
open FStar.Monotonic.Pure

let test (t1:Type u#a) (t2:Type u#b) : (_:t1 -> ND t2 (as_pure_wp (fun p -> True))) = admit()

class ml (t:Type) = { mldummy: unit }

instance ml_totarrow (t1:Type u#a) (t2:Type u#b) {| ml t1 |} {| ml t2 |} : ml (t1 -> Tot t2) =
  { mldummy = () }

instance ml_ndarrow (t1:Type u#a) (t2:Type u#b) {| ml t1 |} {| ml t2 |} : ml (t1 -> ND t2 (as_pure_wp (fun p -> True))) =
  { mldummy = () }

