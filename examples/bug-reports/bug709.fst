module Bug709

let st (s:Type) (a:Type) = s -> M (a * s)

let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0

let bind_st (s:Type) (a:Type) (b:Type)
            (f:st s a) (g:a -> Tot (st s b)) : st s b =
  fun s0 -> let x, s1 = f s0 in g x s1

new_effect {
  STATE (s:Type) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
}
