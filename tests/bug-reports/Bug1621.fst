module Bug1621

let st (s:Type) (a:Type) = s -> M (a * s)
let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0
let bind_st (s:Type) (a:Type) (b:Type) (f:st s a) (g:a -> st s b) : st s b
  = fun (s0:s) -> let (x,s) = f s0 in g x s
let get (s:Type) () : st s s = fun s0 -> s0, s0

total reifiable reflectable new_effect {
  STATE_h (s:Type0) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
     ; get (i:int) = get s
}

new_effect STATE_int = STATE_h int
