module Bug331

(*
type list1 (a:Type) =
  | Nil1 : list1 a
  | Cons1: hd:a -> tl:list2 a -> list1 a
and list2 (a:Type) =
  | List: t:uint8{t=0uy \/ t=1uy} ->
           v:list1 a{ (t=0uy <==> is_Nil1 v)
                     /\ (t=1uy <==> is_Cons1 v) } ->
           list2 a
 *)

module Iso

type list1 (a:Type) =
  | Nil1 : list1 a
  | Cons1: hd:a -> tl:list2 a -> list1 a
and list2 (a:Type) =
  | Nil2: list2 a
  | Cons2: hd:a -> tl:list1 a -> list2 a

module Index

type list1 (a:Type) : bool -> Type =
  | Nil1 : list1 a false
  | Cons1: hd:a -> tl:list2 a -> list1 a true
and list2 (a:Type) =
  | List: #b:bool ->
           v:list1 a b ->
           list2 a
