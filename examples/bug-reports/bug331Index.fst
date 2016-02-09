module Bug331Index

type list1 (a:Type) : bool -> Type =
  | Nil1 : list1 a false
  | Cons1: hd:a -> tl:list2 a -> list1 a true
and list2 (a:Type) =
  | List: #b:bool ->
           v:list1 a b ->
           list2 a
