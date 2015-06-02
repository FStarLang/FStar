(*--build-config
    options:;
    other-files:
 --*)

module Stack
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type Stack (a:Type) = list a
assume logic val push : #a:Type -> Stack a -> a -> Tot (Stack a)
assume logic val pop : #a:Type -> Stack a -> Tot (option (a * (Stack a)))
assume logic val top : #a:Type -> Stack a -> Tot (option (a * (Stack a)))
assume logic val btail : #a:Type -> Stack a -> Tot (Stack a)

type isTop (#a : Type) (t:a) (s : Stack a)  = (top s == (Some t))