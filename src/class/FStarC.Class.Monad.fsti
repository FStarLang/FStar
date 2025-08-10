module FStarC.Class.Monad

open FStarC
open FStarC.Effect

class monad (m : Type -> Type) = {
   return : #a:Type -> a -> m a;
   bind   : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b
}

(* Aliases. Need to declare a very precise type for them. *)
let ( let! ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type -> #b:Type -> m a -> (a -> m b) -> m b = bind
let ( >>=  ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type -> #b:Type -> m a -> (a -> m b) -> m b = bind

inline_for_extraction
let ( >=> ) #m {| monad m |} #a #b #c
  (f : a -> m b) (g : b -> m c) :  a -> m c =
  fun x -> f x >>= g

instance val monad_option : monad option
instance val monad_list   : monad list

val mapM
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> m b) -> list a -> m (list b)

val mapMi
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (int -> a -> m b) -> list a -> m (list b)

val map_optM
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> m b) -> option a -> m (option b)

val iterM
  (#m: Type -> Type)
  {| monad m |}
  (#a :Type)
: (a -> m unit) -> list a -> m unit

val foldM_left
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b -> m a) -> a -> list b -> m a

val foldM_right
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b -> m b) -> list a -> b -> m b

val (<$>) 
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b) -> m a -> m b

val (<*>) 
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: m (a -> b) -> m a -> m b

val fmap
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
  (f : a -> b)
: m a -> m b
