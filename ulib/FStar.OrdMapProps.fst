module FStar.OrdMapProps
 
open FStar.OrdMap

val fold: #k:eqtype -> #v:Type -> #a:Type -> #f:cmp k -> (k -> v -> a -> Tot a)
          -> m:ordmap k v f -> a -> Tot a (decreases (size m))
let rec fold #k #v #t #f g m a =
  if size m = 0 then a
  else
    let Some (k, v) = choose m in
    fold g (remove k m) (g k v a)
