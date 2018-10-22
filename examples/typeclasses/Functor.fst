module Functor

open FStar.Tactics.Typeclasses

class functor f = {
  fmap : (#a:Type) -> (#b:Type) -> (a -> b) -> f a -> f b ;
}

(* Two concrete instances *)
instance functor_list : functor list = { fmap = List.Tot.map }
instance functor_id : functor id = { fmap = fun #_ #_ f a -> f a }

let compose t1 t2 = fun x -> t1 (t2 x)

instance comp #ff #gg (_ : functor ff) (_ : functor gg) : functor (compose ff gg) =
  { fmap = (fun #a #b f x -> fmap #_ #_ #ff (fmap #_ #_ #gg f) x) }

let t1 = fmap #_ #_ #list (fun x -> x + 1) [1 ; 2 ; 3]

let t2 = fmap #_ #_ #(compose list list) (fun x -> x + 1) [[1] ; [2 ; 3]]

let fmap' (#f:Type -> Type) [| functor f |] (#a:Type) (#b:Type) (g:a -> b) (x: f a) : f b =
  fmap #_ #_ #f g x
