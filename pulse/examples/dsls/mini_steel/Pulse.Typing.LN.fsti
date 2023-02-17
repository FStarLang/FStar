module Pulse.Typing.LN
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing

val src_typing_ln (#f:_) (#g:_) (#t:_) (#c:_)
                  (d:src_typing f g t c)
  : Lemma (ln t /\ ln_c c)


val src_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
                        (d:src_typing f g t c)
                        (x:var)
  : Lemma 
    (requires x `Set.mem` freevars t \/
              x `Set.mem` freevars_comp c)
    (ensures Some? (lookup g x))


let src_typing_freevars_inv (#f:_) (#g:_) (#t:_) (#c:_)
                        (d:src_typing f g t c)
                        (x:var)
  : Lemma 
    (requires None? (lookup g x))
    (ensures ~(x `Set.mem` freevars t) /\
             ~(x `Set.mem` freevars_comp c))
  = if x `Set.mem` freevars t
    ||  x `Set.mem` freevars_comp c
    then src_typing_freevars d x
