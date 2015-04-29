module Bug210c

assume val acc_inv : aa:Type -> a:int -> Tot (e:int{e = a})

val fix_F : a:int -> Tot unit
let fix_F a = assert(acc_inv a = a)
