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
