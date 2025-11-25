module Bug3991

noeq
type mytc (#a:Type0) (s:a) = | X

let mytc_let_rec : mytc (let rec f x = x in ()) = X

let rec foo (x:int) : int = x

let _ = assert (forall x. 1 + x > x)
