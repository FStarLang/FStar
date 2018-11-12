module Bug117

noeq type r : Type -> Type =
  | C1 : t:Type -> int -> r t
  | C2 : t:Type -> int -> int -> r t

let foo h =
  match h with
  | C1 _ _
  | C2 _ _ _ -> ()
