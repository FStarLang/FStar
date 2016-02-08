module Unit1.WPsAndTriples
type as_requires (#a:Type) (wp:PureWP a)  = wp (fun x -> True)
type as_ensures  (#a:Type) (wlp:PureWP a) (x:a) = ~ (wlp (fun y -> ~(y=x)))
assume val as_Pure: #a:Type -> #b:(a -> Type)
          -> #wp:(x:a -> PureWP (b x))
          -> #wlp:(x:a -> PureWP (b x))
          -> =f:(x:a -> PURE (b x) (wp x) (wlp x))
          -> x:a -> Pure (b x) (as_requires (wp x))
                               (as_ensures (wlp x))

val f : x:int -> PURE int (fun 'p -> x > 0 /\ 'p (x + 1)) (fun 'p -> x > 0 ==> 'p (x + 1))
let f x = assert (x > 0); x + 1

val h : #req:(int -> Type) -> #ens:(int -> int -> Type) -> =f:(x:int -> Pure int (req x) (ens x)) -> y:int -> Pure int (req y) (ens y)
let h f x = f x

val g : x:int -> Pure int (x > 0) (fun y -> y == x + 1)
let g = h (as_Pure f)
