module Bug1640

open FStar.Reflection

let _ = assert (inspect_ln (`()) == Tv_Const C_Unit)
