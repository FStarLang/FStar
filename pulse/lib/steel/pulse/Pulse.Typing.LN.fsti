module Pulse.Typing.LN
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

val tot_typing_ln (#g:_) (#e:_) (#t:_)
                  (d:tot_typing g e t)
  : Lemma (ln e /\ ln t)

val comp_typing_ln (#g:_) (#c:_) (#u:_)
                   (d:comp_typing g c u)
  : Lemma (ln_c c)

val st_typing_ln  (#g:_) (#t:_) (#c:_)
                  (st:st_typing g t c)
  : Lemma (ln_st t /\ ln_c c)
