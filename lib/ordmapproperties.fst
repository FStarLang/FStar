(*--build-config
    options:--admit_fsi OrdSet --admit_fsi OrdMap;
    other-files:ordset.fsi ordmap.fsi
 --*)
module FStar.OrdMapProps
 
open FStar.OrdMap

val fold: #k:Type -> #v:Type -> #a:Type -> #f:cmp k -> (k -> v -> a -> Tot a)
          -> m:ordmap k v f -> a -> Tot a (decreases (size m))
let rec fold (#k:Type) (#v:Type) #f g m a =
  if m = empty then a
  else
    let Some (k, v) = choose m in
    fold g (remove k m) (g k v a)

(**********)
