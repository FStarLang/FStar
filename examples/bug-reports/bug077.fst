module Bug077

assume type a
assume type p : a -> Type

val ok : x:a{p x} -> r:a{p r}
let ok x = x

val ok2 : x:a{p x} -> r:(option a){Some? r ==> p (Some?.v r)}
let ok2 x = Some x

val ok3 : x:a{p x} -> option (r:a{p r})
let ok3 x = Some x


assume type b
assume type q : a -> b -> Type

val ok4 : x:a -> y:b{q x y} -> r:(a * b){q (fst r) (snd r)}
let ok4 x y = (x, y)

val ok5 : x:a -> y:b{q x y} -> r:(option (a * b)){Some? r ==> q (fst (Some?.v r)) (snd (Some?.v r))}
let ok5 x y = Some (x, y)

val bug : x:a -> y:b{q x y} -> option (r:(a * b){q (fst r) (snd r)})
let bug x y = Some (x, y)
