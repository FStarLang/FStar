module Bug575

type relation = int -> Type

type multi (r:relation) : int -> Type =
| Multi_step : x:int -> r x -> multi r x
