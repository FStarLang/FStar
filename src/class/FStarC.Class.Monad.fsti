module FStarC.Class.Monad

open FStarC
open FStarC.Effect

class monad (m : Type -> Type) = {
   return : #a:Type -> a -> m a;
   bind   : #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b)
}

(* Aliases. Need to declare a very precise type for them. *)
let ( let! ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b) = bind
let ( >>=  ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type -> #b:Type -> m a -> (a -> ML (m b)) -> ML (m b) = bind

inline_for_extraction
let ( >=> ) #m {| monad m |} #a #b #c
  (f : a -> ML (m b)) (g : b -> ML (m c)) :  a -> ML (m c) =
  fun x -> f x >>= g

instance val monad_option : monad option
instance val monad_list   : monad list

val mapM
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> ML (m b)) -> list a -> ML (m (list b))

val mapMi
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (int -> a -> ML (m b)) -> list a -> ML (m (list b))

val map_optM
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> ML (m b)) -> option a -> ML (m (option b))

val iterM
  (#m: Type -> Type)
  {| monad m |}
  (#a :Type)
: (a -> ML (m unit)) -> list a -> ML (m unit)

val foldM_left
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b -> ML (m a)) -> a -> list b -> ML (m a)

val foldM_right
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b -> ML (m b)) -> list a -> b -> ML (m b)

val (<$>) 
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> b) -> m a -> ML (m b)

val (<*>) 
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: m (a -> b) -> m a -> ML (m b)

val fmap
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
  (f : a -> b)
: m a -> ML (m b)
