module FStar.ConstantTimeSequence.Base

val seq (a:Type u#a) : Type u#a

val of_list (#a:Type u#a) (l:list a) : Tot (seq a)

val length (#a:Type) (s:seq a) : Tot nat

val index (#a:Type) (s:seq a) (i:nat { i < length s }) : Tot a
