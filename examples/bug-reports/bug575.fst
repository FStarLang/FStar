module Bug575

type relation = int -> Type0

// This works
noeq type multi0 (r:int -> Type0) : int -> Type =
| Multi_step0 : x:int -> r x -> multi0 r x

// Unexpected error
noeq type multi (r:relation) : int -> Type =
| Multi_step : x:int -> r x -> multi r x
