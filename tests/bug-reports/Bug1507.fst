module Bug1507

noeq
type mu (f: Type -> Type) = 
    | Mu of f (mu f)
