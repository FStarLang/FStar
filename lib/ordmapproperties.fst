(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap;
    other-files:ordset.fsi ordmap.fsi
 --*)
module OrdMapProps
 
open OrdMap

val fold: #key:Type -> #value:Type -> #a:Type -> f:cmp key -> (key -> value -> a -> Tot a)
          -> m:ordmap key value f -> a
          -> Tot a (decreases (size f m))
let rec fold f g m a =
  if m = empty f then a
  else
    let Some (k, v) = choose f m in
    fold f g (remove f k m) (g k v a)

(**********)
