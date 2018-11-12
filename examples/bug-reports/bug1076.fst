module Bug1076

assume val t:Type

noeq type inductive =
  | Const0 : inductive
  | Const1 : t -> inductive
