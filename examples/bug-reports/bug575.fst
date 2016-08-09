module Bug575

type relation = int -> Type0

// Used work when originally filing this bug, now no longer
type multi0 (r:int -> Type0) : int -> Type =
| Multi_step0 : x:int -> r x -> multi0 r x

// Unexpected error
type multi (r:relation) : int -> Type =
| Multi_step : x:int -> r x -> multi r x
