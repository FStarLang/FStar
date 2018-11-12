module Bug189

type heap = unit -> Tot unit

type pred = heap -> Tot unit

type deduce : unit -> Type =
| Blah : deduce ()

val feq : #a:Type -> a -> Tot unit
let feq x = ()

type hoare_c (q:pred) = (h':heap -> deduce (q h'))

val skip_spec : u:unit -> Tot (hoare_c feq)
let skip_spec u = fun h1 -> magic()
