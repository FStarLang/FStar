module RefNew

open FStar.Ref

let _test (x:int) = assert (ref int =!= int)
