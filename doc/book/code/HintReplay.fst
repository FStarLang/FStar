module HintReplay

assume
val p (x:int) : prop

assume
val q (x:int) : prop

assume
val r (x:int) : prop

assume P_Q : forall (x:int). {:pattern q x} q x ==> p x
assume Q_R : forall (x:int). {:pattern p x} q x ==> r x

let test (x:int { q x }) = assert (r x)
