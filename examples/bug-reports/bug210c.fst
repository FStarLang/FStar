module Bug210c

(* Removing the aa argument to acc_inv makes this work. *)
assume val acc_inv : #aa:Type -> a:int -> Tot (e:int{e = a})

val fix_F : a:int -> Tot unit
let fix_F a = assert(acc_inv a = a)
