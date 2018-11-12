module Bug736

noeq type goal : Type =
| Goal : #a:Type -> a -> goal
| AHyp : #a:Type -> option a -> (a -> Tot goal) -> goal
