module Bug097b

assume val f : list 'a -> Tot nat

assume val g: l:list 'a -> n:int{n >= 0 /\ n < (f l)} -> Tot 'a
