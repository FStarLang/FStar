(*--build-config
  --*)
module PrimsNonPrim

type l_or   (p:Type) (q:Type) =
  | Left : p -> l_or p q
  | Right : q -> l_or p q


  type l_and  (p:Type) (q:Type) =
    | And : p -> q -> l_and p q

type b2t (b:bool) = b==true

type True =
      | T

type False =

opaque type l_imp (p:Type) (q:Type) = p -> Tot q

type l_iff (p:Type) (q:Type) = l_and (l_imp p q)  (l_imp q p)        (* infix binary '<==>' *)
type l_not (p:Type) = l_imp p  False                        (* prefix unary '~' *)


type Forall (#a:Type) (p:a -> Type) = x:a -> Tot (p x)   (* forall (x:a). p x *)

type ForallTyp (f : Type -> Type) = (t:Type) -> Tot (f t)

type Exists (#a:Type) (p:a -> Type) =
| MkExists : av:a -> pr:(p av) -> Exists p
   (* forall (x:a). p x *)
