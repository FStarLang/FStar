module Bug1486

open FStar.Tactics.Typeclasses

noeq type functor f = {
  fmap  : (#a:Type) -> (#b:Type) -> (a -> b) -> f a -> f b ;
}

%splice[fmap] (mk_class (`%functor))

(* Two concrete instances *)
[@instance] let functor_list : functor list = { fmap = List.Tot.map }
[@instance] let functor_id : functor id = { fmap = fun #_ #_ f a -> f a }

let _ = fmap (fun x -> x + 1) [1 ; 2 ; 3]

let fmap' (#f:Type -> Type) [| functor f |] (#a:Type) (#b:Type) (g:a -> b) (x: f a) : f b = fmap g x
