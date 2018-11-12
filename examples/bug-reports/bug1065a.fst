module Bug1065a

assume type mem

let st_pre = st_pre_h mem
let st_post' (a:Type) (pre:Type) = st_post_h' mem a pre

assume val myStack : (a:Type) -> (pre:st_pre) -> (post: (m0:mem -> Tot (st_post' a (pre m0)))) -> Type0

assume val gg : #a:Type -> #pre:(st_pre_h mem) -> #post:(mem -> Tot (st_post_h' mem a True)) -> myStack a pre post
