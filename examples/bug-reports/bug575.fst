module Bug575

type relation = int -> Type0

// This works
noeq type multi0 (r:int -> Type0) : int -> Type =
| Multi_step0 : x:int -> r x -> multi0 r x

// Unexpected error
noeq type multi (r:relation) : int -> Type u#1 =
| Multi_step : x:int -> r x -> multi r x

(* unexpected error even with --__temp_no_proj *)
let Multi_step? r x (projectee : multi r x) =
  match projectee with
	  | Multi_step _ _  -> true
	  | _  -> false
