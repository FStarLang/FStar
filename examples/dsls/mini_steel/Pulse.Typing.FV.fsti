module Pulse.Typing.FV
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing

let mem_intension_pat (#a:eqtype) (x:a) (f:(a -> Tot bool))
  : Lemma
    (ensures FStar.Set.(mem x (intension f) = f x))
    [SMTPat FStar.Set.(mem x (intension f))]
  = Set.mem_intension x f

let contains (g:env) (x:var) = Some? (lookup g x)
let vars_of_env (g:env) = Set.intension (contains g)

let set_minus (#a:eqtype) (s:Set.set a) (x:a) =
  Set.intersect s (Set.complement (Set.singleton x))

val freevars_close_term (e:term) (x:var) (i:index)
  : Lemma 
    (ensures freevars (close_term' e x i) ==
             freevars e `set_minus` x)
    [SMTPat (freevars (close_term' e x i))]


val st_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
                       (d:st_typing f g t c)
  : Lemma 
    (ensures freevars_st t `Set.subset` vars_of_env g /\
             freevars_comp c `Set.subset` vars_of_env g)


let st_typing_freevars_inv (#f:_) (#g:_) (#t:_) (#c:_)
                           (d:st_typing f g t c)
                           (x:var)
  : Lemma 
    (requires None? (lookup g x))
    (ensures ~(x `Set.mem` freevars_st t) /\
             ~(x `Set.mem` freevars_comp c))
  = st_typing_freevars d
