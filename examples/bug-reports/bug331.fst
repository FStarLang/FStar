module Bug331

(*
type list1 (a:Type) =
  | Nil1 : list1 a
  | Cons1: hd:a -> tl:list2 a -> list1 a
and list2 (a:Type) =
  | List: t:uint8{t=0uy \/ t=1uy} ->
           v:list1 a{ (t=0uy <==> Nil1? v)
                     /\ (t=1uy <==> Cons1? v) } ->
           list2 a
 *)
