(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Benton2004.SmithVolpano
include Benton2004.DDCC

type seclevel = | Low | High

let interp_seclevel (t: Type0) (s: seclevel) : GTot (nstype t) =
  match s with
  | Low -> ns_delta
  | High -> ns_t

type context = (l: list (var * seclevel) { List.Tot.noRepeats (List.Tot.map fst l) } )

let rec interp_context
  (gamma: context)
: Ghost sttype
  (requires True)
  (ensures (fun phi -> forall x' . List.Tot.mem x' (List.Tot.map fst gamma) == false ==> x' `st_fresh_in` phi))
=  match gamma with
  | [] -> st_nil
  | (x, s) :: gamma' -> st_cons (interp_context gamma') x (interp_seclevel int s)

abstract
let eval_equiv
  (#t: Type0)
  (c: context)
  (f: exp t)
  (s: seclevel)
: GTot Type0
= Benton2004.DDCC.eval_equiv (interp_context c) (interp_seclevel _ s) f f

let eval_equiv_def
  (#t: Type0)
  (gamma: context)
  (f: exp t)
  (s: seclevel)
: Lemma
  (eval_equiv gamma f s <==> Benton2004.DDCC.eval_equiv (interp_context gamma) (interp_seclevel _ s) f f)
= ()

abstract
let exec_equiv
  (gamma: context)
  (c: computation)
  (s: seclevel)
: GTot Type0
= Benton2004.DDCC.exec_equiv (interp_context gamma) (interp_context gamma) c (match s with Low -> c | High -> skip)

let exec_equiv_def
  (gamma: context)
  (c: computation)
  (s: seclevel)
: Lemma
  (exec_equiv gamma c s <==> Benton2004.DDCC.exec_equiv (interp_context gamma) (interp_context gamma) c (match s with Low -> c | High -> skip))
= ()

(* Figure 4 *)

let fresh_in (x: var) (gamma: context) : GTot Type0 =
  List.Tot.mem x (List.Tot.map fst gamma) == false

let eval_equiv_var_same
  (gamma: context)
  (x: var)
  (s: seclevel)
: Lemma
  (requires (x `fresh_in` gamma))
  (ensures (
    x `fresh_in` gamma /\
    eval_equiv ((x, s) :: gamma) (evar x) s
  ))
  [SMTPat (eval_equiv ((x, s)::gamma) (evar x) s)]
= d_v x (interp_context gamma) (interp_seclevel int s)

let eval_equiv_var_other
  (gamma: context)
  (x y: var)
  (sx sy: seclevel)
: Lemma
  (requires (
    y `fresh_in` gamma /\
    x <> y /\
    eval_equiv gamma (evar x) sx
  ))
  (ensures (
    y `fresh_in` gamma /\
    eval_equiv ((y, sy) :: gamma) (evar x) sx
  ))
  [SMTPat (eval_equiv ((y, sy)::gamma) (evar x) sx)]
= ()

let eval_equiv_const
  (#t: Type0)
  (gamma: context)
  (c: t)
  (s: seclevel)
: Lemma
  (eval_equiv gamma (const c) s)
  [SMTPat (eval_equiv gamma (const c) s)]
= Benton2004.DDCC.eval_equiv_const c (interp_context gamma)

let op_abs_interp_seclevel
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (s: seclevel)
: Lemma
  (op_abs op (interp_seclevel _ s) (interp_seclevel _ s) (interp_seclevel _ s))
= ()

let eval_equiv_op
  (#from #to: Type0)
  (op: (from -> from -> Tot to))
  (gamma: context)
  (e e' : exp from)
  (s: seclevel)
: Lemma
  (requires (
    eval_equiv gamma e s /\
    eval_equiv gamma e' s
  ))
  (ensures (eval_equiv gamma (eop op e e') s))
  [SMTPat (eval_equiv gamma (eop op e e') s)]  
= op_abs_interp_seclevel op s;
  d_op op e e e' e' (interp_seclevel _ s) (interp_seclevel _ s) (interp_seclevel _ s) (interp_context gamma)

let exec_equiv_assign
  (gamma: context)
  (x: var)
  (e: exp int)
  (s: seclevel)
: Lemma
  (requires (
    x `fresh_in` gamma /\
    eval_equiv ((x, s)::gamma) e s
  ))
  (ensures (
    x `fresh_in` gamma /\
    exec_equiv ((x, s)::gamma) (assign x e) s
  ))
  [SMTPat (exec_equiv ((x, s)::gamma) (assign x e) s)]
= match s with
  | Low -> d_assign (interp_context gamma) x (interp_seclevel _ s) (interp_seclevel _ s) e e
  | High -> d_das x e (interp_context gamma) (interp_seclevel _ s) 

let exec_equiv_seq
  (gamma: context)
  (c c' : computation)
  (s: seclevel)
: Lemma
  (requires (
    exec_equiv gamma c s /\
    exec_equiv gamma c' s
  ))
  (ensures (
    exec_equiv gamma (seq c c') s
  ))
  [SMTPat (exec_equiv gamma (seq c c') s)]
= match s with
  | Low -> ()
  | High -> d_su1' c c' skip (interp_context gamma) (interp_context gamma) (interp_context gamma) // FIXME: WHY WHY WHY does this pattern NOT trigger?
  

let exec_equiv_ifthenelse
  (gamma: context)
  (b: exp bool)
  (c c' : computation)
  (s: seclevel)
: Lemma
  (requires (
    eval_equiv gamma b s /\
    exec_equiv gamma c s /\
    exec_equiv gamma c' s
  ))
  (ensures (exec_equiv gamma (ifthenelse b c c') s))
  [SMTPat (exec_equiv gamma (ifthenelse b c c') s)]
= ()

let exec_equiv_while
  (gamma: context)
  (b: exp bool)
  (c: computation)
: Lemma
  (requires (
    eval_equiv gamma b Low /\
    exec_equiv gamma c Low
  ))
  (ensures (exec_equiv gamma (while b c) Low))
  [SMTPat (exec_equiv gamma (while b c) Low)]
= ()

let eval_equiv_low_to_high
  (#t: Type0)
  (gamma: context)
  (e: exp t)
: Lemma
  (requires (eval_equiv gamma e Low))
  (ensures (eval_equiv gamma e High))
  [SMTPat (eval_equiv gamma e High)]
= ()

let exec_equiv_high_to_low
  (gamma: context)
  (c: computation)
: Lemma
  (requires (exec_equiv gamma c High))
  (ensures (exec_equiv gamma c Low))
  [SMTPat (exec_equiv gamma c Low)]
= ()

(* Definition 2 *)

let strong_sequential_noninterference
  (gamma: context)
  (c: computation)
: GTot Type0
= exec_equiv gamma c Low
  
