module FStar.Custard

let no_specialize : unit = ()

[@@ no_specialize]
let dyn (#a:Type) (x:a) : Pure a (requires True) (ensures fun r -> r == x) = x
