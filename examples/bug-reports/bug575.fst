module Bug575

type relation = int -> Type0

// Works
type multi0 (r:int -> Type0) : int -> Type =
| Multi_step0 : x:int -> r x -> multi0 r x

// Gets stuck
type multi (r:relation) : int -> Type =
| Multi_step : x:int -> r x -> multi r x
