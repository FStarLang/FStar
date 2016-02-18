module Bug362
type t = | C : (t -> Type) -> t
