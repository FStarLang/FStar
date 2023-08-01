module Bug1640

open FStar.Reflection.V2

let _ = assert (inspect_ln (`()) == Tv_Const C_Unit)
