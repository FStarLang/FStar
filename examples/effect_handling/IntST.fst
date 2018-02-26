module IntST

let st t = int -> t * int

let return (#a:Type) (x : a) : st a =
  fun s -> (x, s)

let bind (#a:Type) (#b:Type) (m : st a) (f : a -> st b) : st b =
  fun s -> let (x, s') = m s in f x s'

let get () : st int =
  fun s -> (s, s)

let put (s : int) : st unit =
  fun _ -> ((), s)
