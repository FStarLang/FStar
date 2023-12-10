module FStar.Class.Monad

open FStar.Compiler
open FStar.Compiler.Effect

class monad (m : Type -> Type) = {
   return : #a:Type -> a -> m a;
   ( let! )  : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b
}

instance val monad_option : monad option

val mapM
  (#m: Type -> Type)
  {| monad m |}
  (#a #b :Type)
: (a -> m b) -> list a -> m (list b)

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