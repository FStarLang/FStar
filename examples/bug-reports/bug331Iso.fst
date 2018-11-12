module Bug331Iso

type list1 (a:Type) =
  | Nil1 : list1 a
  | Cons1: hd:a -> tl:list2 a -> list1 a
and list2 (a:Type) =
  | Nil2: list2 a
  | Cons2: hd:a -> tl:list1 a -> list2 a
