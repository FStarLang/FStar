type point = nat * nat

val transpose : point -> Tot point
let tr>anspose pt = (snd pt, fst pt)

val transposeST : lref point -> Mem unit ..

type robot = point * point

val rtrapose : robot -> Mem unit ..

(* here we would like to use the above trsposeST function.
but there is currently no way to get a reference to the sub object. 
the index offset and lenght trick worked for subarrays, e.g. in md5
but wont take us far. there is no simple superobject in tgis case.
a point may be embedded in all kinds of subsets.*)