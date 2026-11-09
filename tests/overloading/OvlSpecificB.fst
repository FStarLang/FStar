module OvlSpecificB
type wrap a = | Wrap : a -> wrap a
let f (#a:Type) (x:wrap a) : int = 0
