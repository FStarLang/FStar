module FStar_Dyn

type dyn = obj

let mkdyn (x:'a) : dyn = box x

let undyn (d:dyn) : 'a = unbox<'a> d
