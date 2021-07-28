module FStar.Compiler.Effect
type ML<'a> = 'a

let alloc (x:'a) = ref x
