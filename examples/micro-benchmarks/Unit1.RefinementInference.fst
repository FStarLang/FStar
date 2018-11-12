module Unit1.RefinementInference
assume type erased : Type -> Type
assume val reveal: erased 'a -> GTot 'a
assume val consHd : #a:Type -> l:list a{Cons? l} -> Tot a
assume val elift1_p : #a:Type -> #b:Type -> #p:(a -> GTot Type) -> 
		      $f:(x:a{p x} -> Tot b) -> 
		      r:erased a{p (reveal r) } -> 
		      Tot (erased b)

val ghostConsHd : a:Type -> l:erased (list a){Cons? (reveal l)} -> Tot (erased a)
let ghostConsHd (a:Type) l = elift1_p consHd l
