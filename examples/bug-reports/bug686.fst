module Bug686

type bidule : (a:Type) -> a -> Tot Type =
| Chose : bidule unit ()

// everything works fine if we ask for unification on f ($f)
let truc (#a:Type) (f: a -> Tot Type) : unit = ()


// Unknown assertion failed
let test_wrong : unit = truc (bidule unit)
