(*
   Copyright 2025 Microsoft Research

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
module Part3.DataTypesALaCarte
open FStar.Mul
open FStar.Tactics.Typeclasses
#set-options "--z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100' --fuel 2 --ifuel 2"
(**
 * This module is an adaptation of W. Swierstra's Data Type a la Carte
 * https://www.cambridge.org/core/journals/journal-of-functional-programming/article/data-types-a-la-carte/14416CB20C4637164EA9F77097909409
 * 
 * Demonstrating extensibility of datatypes and functions over them, 
 * defined generically as sums/coproducts of functors,
 * with typeclasses to smoothen their use.
 *
 * The main adaptation is to convince F*'s termination checker:
 *  -- The functor signatures are decorated with strict positivity attributes
 *  -- The fmap signature forces the map to be applied only on strictly smaller arguments
 *
 *)

//SNIPPET_START: exp$
type exp =
| V of int
| Plus : exp -> exp -> exp

let rec evaluate = function
| V i -> i
| Plus e1 e2 -> evaluate e1 + evaluate e2
//SNIPPET_END: exp$


//SNIPPET_START: expr-fail$
[@@expect_failure]
noeq
type expr (f : (Type -> Type)) =
  | In of f (expr f)
//SNIPPET_END: expr-fail$

//SNIPPET_START: expr$
noeq
type expr (f : ([@@@strictly_positive]Type -> Type)) =
  | In of f (expr f)
//SNIPPET_END: expr$

//SNIPPET_START: elist$
type list ([@@@strictly_positive]a:Type) =
| Nil
| Cons : a -> list a -> list a

let elist = expr list

(*
   .___ Nil
  /
 .
  \.___.____Nil
*)
let elist_ex1 = 
  In (Cons (In Nil) 
           (Cons (In (Cons (In Nil) Nil)) 
            Nil))
//SNIPPET_END: elist$

//SNIPPET_START: coprod$
noeq
type coprod (f g: ([@@@strictly_positive]Type -> Type)) ([@@@strictly_positive]a:Type) =
  | Inl of f a
  | Inr of g a
let ( ++ ) f g = coprod f g
//SNIPPET_END: coprod$

//SNIPPET_START: value add$
type value ([@@@strictly_positive]a:Type) =
  | Val of int

type add ([@@@strictly_positive]a:Type) =
  | Add : a -> a -> add a

let addExample : expr (value ++ add) = In (Inr (Add (In (Inl (Val 118))) (In (Inl (Val 1219)))))
//SNIPPET_END: value add$

// Injections and projections to build values more easily

//SNIPPET_START: inj_proj$
let inj_t (f g:Type -> Type) = #a:Type -> f a -> g a
let proj_t (f g:Type -> Type) = #a:Type -> x:g a -> option (f a)
//SNIPPET_END: inj_proj$

//SNIPPET_START: leq$
class leq (f g : [@@@strictly_positive]Type -> Type) = {
  inj: inj_t f g;
  proj: proj_t f g;
  inversion: unit
   -> Lemma (
    (forall (a:Type) (x:g a).
      match proj x with
      | Some y -> inj y == x
      | _ -> True) /\
    (forall (a:Type) (x:f a). 
      proj (inj x) == Some x)
  )
}
//SNIPPET_END: leq$

//SNIPPET_START: leq_refl$
instance leq_refl f : leq f f = {
  inj=(fun #_ x -> x);
  proj=(fun #_ x -> Some x);
  inversion=(fun _ -> ())
}
//SNIPPET_END: leq_refl$

//SNIPPET_START: leq_ext_left$
instance leq_ext_left f g
: leq f (g ++ f)
= let inj : inj_t f (g ++ f) = Inr in 
  let proj : proj_t f (g ++ f) = fun #a x ->
    match x with
    | Inl _ -> None
    | Inr x -> Some x
  in
  { inj; proj; inversion=(fun _ -> ()) }
//SNIPPET_END: leq_ext_left$

//SNIPPET_START: leq_cong_right$
instance leq_cong_right 
  f g h
  {| f_inj:leq f h |}
: leq f (h ++ g)
= let inj : inj_t f (h ++ g) = fun #a x -> Inl (f_inj.inj x) in
  let proj : proj_t f (h ++ g) = fun #a x -> 
    match x with
    | Inl x -> f_inj.proj x
    | _ -> None
  in
  { inj; proj; inversion=(fun _ -> f_inj.inversion()) }
//SNIPPET_END: leq_cong_right$

//SNIPPET_START: inject project$
let compose (#a #b #c:Type) (f:b -> c) (g: a -> b) (x:a) : c = f (g x)
let inject #f #g {| gf: leq g f |}
: g (expr f) -> expr f 
= compose In gf.inj

let project #g #f {| gf: leq g f |}
: x:expr f -> option (g (expr f)) 
= fun (In x) -> gf.proj x

let inject_project 
  #f #g {| gf: leq g f |}
  (x:expr f)
: Lemma (
    match project #g #f x with
    | Some y -> inject y == x
    | _ -> True
) [SMTPat (project #g #f x)]
= gf.inversion()

let project_inject #f #g {| gf: leq g f |} (x:g (expr f))
: Lemma (
    project #g #f (inject x) == Some x
) [SMTPat (project #g #f (inject x))]
= gf.inversion()
//SNIPPET_END: inject project$

//SNIPPET_START: v and +^$
let v #f {| vf: leq value f |} (x:int)
: expr f
= inject (Val x)

let ( +^ ) #f {| vf : leq add f |} (x y: expr f)
: expr f
= inject (Add x y)
//SNIPPET_END: v and +^$

//SNIPPET_START: ex1$
let ex1 : expr (value ++ add) = v 118 +^ v 1219
//SNIPPET_END: ex1$

//SNIPPET_START: mul$
type mul ([@@@strictly_positive]a:Type) =
  | Mul : a -> a -> mul a

let ( *^ ) #f {| vf : leq mul f |} (x y: expr f)
: expr f
= inject (Mul x y)

let ex2 : expr (value ++ add ++ mul) = v 1001 +^ v 1833 +^ v 13713 *^ v 24
//SNIPPET_END: mul$

/// Evaluating expressions

//SNIPPET_START: functor$
class functor (f:[@@@strictly_positive]Type -> Type) = {
  fmap : (#a:Type -> #b:Type -> x:f a -> (y:a{y << x} -> b) -> f b)
}
//SNIPPET_END: functor$

//SNIPPET_START: functor_value$
instance functor_value : functor value =
  let fmap (#a #b:Type) (x:value a) (f:(y:a{y<<x} -> b)) : value b =
    let Val x = x in Val x
  in
  { fmap }
//SNIPPET_END: functor_value$

//SNIPPET_START: functor_add$
instance functor_add : functor add =
  let fmap (#a #b:Type) (x:add a) (f:(y:a{y<<x} -> b)) : add b =
    let Add x y = x in
    Add (f x) (f y)
  in
  { fmap }
//SNIPPET_END: functor_add$

//SNIPPET_START: functor_mul$
instance functor_mul : functor mul = 
  let fmap (#a #b:Type) (x:mul a) (f:(y:a{y<<x} -> b)) : mul b =
    let Mul x y = x in
    Mul (f x) (f y)
  in
  { fmap }
//SNIPPET_END: functor_mul$

//SNIPPET_START: functor_coprod$
instance functor_coprod 
    #f #g
    {| ff: functor f |} {| fg: functor g |}
: functor (coprod f g)
= let fmap (#a #b:Type) (x:coprod f g a) (a2b:(y:a{y << x} -> b)) 
  : coprod f g b
  = match x with
    | Inl x -> Inl (ff.fmap x a2b)
    | Inr x -> Inr (fg.fmap x a2b)
  in
  { fmap }
//SNIPPET_END: functor_coprod$

//SNIPPET_START: fold_expr$
let rec fold_expr #f #a {| ff : functor f |}
    (alg:f a -> a) (e:expr f)
: a
= let In t = e in
  alg (fmap t (fun x -> fold_expr alg x))
//SNIPPET_END: fold_expr$

//SNIPPET_START: eval$
class eval (f: [@@@strictly_positive]Type -> Type) = {
  evalAlg : f int -> int
}

instance eval_val : eval value =
  let evalAlg : value int -> int = fun (Val x) -> x in
  { evalAlg }

instance eval_add : eval add =
  let evalAlg : add int -> int = fun (Add x y) -> x + y in
  { evalAlg }

instance eval_mul : eval mul=
  let evalAlg : mul int -> int = fun (Mul x y) -> x * y in
  {  evalAlg }
//SNIPPET_END: eval$

//SNIPPET_START: eval_coprod$
instance eval_coprod 
    #f #g
    {| ef: eval f |}
    {| eg: eval g |} 
: eval (coprod f g)
= let evalAlg (x:coprod f g int) : int =
    match x with
    | Inl x -> ef.evalAlg x
    | Inr y -> eg.evalAlg y
  in
  { evalAlg }
//SNIPPET_END: eval_coprod$

//SNIPPET_START: eval_expr$
let eval_expr  #f {| eval f |} {| functor f |} (x:expr f)
: int = fold_expr evalAlg x
//SNIPPET_END: eval_expr$

//SNIPPET_START: eval_test$
let test = assert_norm (eval_expr ex1 == 1337)
let test2 = assert_norm (eval_expr ex2 == ((1001 + 1833 + 13713 * 24)))
//SNIPPET_END: eval_test$

(* lift allows promoting terms defined in a smaller type to a bigger one *)
let rec lift #f #g
    {| ff: functor f |} 
    {| fg: leq f g |}
    (x: expr f)
: expr g
= let In xx = x in
  let xx : f (expr f) = xx in
  let yy : f (expr g) = ff.fmap xx lift in 
  In (fg.inj yy)

(* reuse addExample by lifting it *)
let ex3 : expr (value ++ add ++ mul) = lift addExample *^ v 2
let test3 = assert_norm (eval_expr ex3 == (1337 * 2))

//////////////////////////////////////////
// Rewrite rules
//////////////////////////////////////////

//SNIPPET_START: rewrite_rule$
let rewrite_rule f = expr f -> option (expr f)
let rewrite_rule_soundness #f (r:rewrite_rule f)
  {| eval f |} {| functor f |} 
  (x:expr f) =
    match r x with
    | None -> True
    | Some y -> eval_expr x == eval_expr y
noeq
type rewrite_t (f:_) {| eval f |} {| functor f |} = {
  rule: rewrite_rule f;
  soundness: unit -> Lemma (forall x. rewrite_rule_soundness rule x)
}
//SNIPPET_END: rewrite_rule$

//SNIPPET_START: error_monad$
let (let?) 
    (x:option 'a) 
    (g:(y:'a { Some y == x} -> option 'b))
: option 'b =
  match x with
  | None -> None
  | Some y -> g y

let return (x:'a) : option 'a = Some x

let dflt (y:'a) (x:option 'a) : 'a =
  match x with
  | None -> y
  | Some x -> x

let or_else (x:option 'a)
            (or_else: squash (None? x) -> 'a)
: 'a
= match x with
  | None -> or_else ()
  | Some y -> y
//SNIPPET_END: error_monad$

//SNIPPET_START: expected_semantics$
let ev_val_sem #f (ev: eval f) {| functor f |} {| leq value f |} =
  forall (x:expr f). dflt True 
    (let? Val a = project x in
     Some (eval_expr x == a))

let ev_add_sem #f (ev: eval f) {| functor f |} {| leq add f |} =
  forall (x:expr f). dflt True 
    (let? Add a b = project x in
     Some (eval_expr x == eval_expr a + eval_expr b))

let ev_mul_sem #f (ev: eval f) {| functor f |} {| leq mul f |} =
  forall (x:expr f). dflt True 
    (let? Mul a b = project x in
     Some (eval_expr x == eval_expr a * eval_expr b))
//SNIPPET_END: expected_semantics$

//SNIPPET_START: distr_mul$
let distr_mul_l #f
    {| ev: eval f |} {| functor f |}
    {| leq add f |} {| leq mul f |}
    (_: squash (ev_add_sem ev /\ ev_mul_sem ev))
: rewrite_t f
= let rule = fun (x:expr f) ->
    let? Mul a b = project x in
    let? Add c d = project b in
    return (a *^ c +^ a *^ d)
  in
  let soundness _ = () in
  { rule; soundness }

let distr_mul_r #f
    {| ev: eval f |} {| functor f |}
    {| leq add f |} {| leq mul f |}
    (_: squash (ev_add_sem ev /\ ev_mul_sem ev))
: rewrite_t f
= let rule = fun x ->
    let? Mul a b = project x in
    let? Add c d = project a in
    return (c *^ b +^ d *^ b)
  in
  let soundness _ = () in
  { rule; soundness }
//SNIPPET_END: distr_mul$

//SNIPPET_START: compose_rewrites$
let compose_rewrites #f
    {| ev: eval f |} {| functor f |}
    (r0 r1: rewrite_t f)
: rewrite_t f
= let rule : expr f -> option (expr f) = fun x ->
    match r0.rule x with
    | None -> r1.rule x
    | x -> x
  in
  let soundness _ 
    : Lemma (forall x. rewrite_rule_soundness rule x)
    = r0.soundness(); r1.soundness()
  in
  { rule; soundness }
//SNIPPET_END: compose_rewrites$

//SNIPPET_START: rewrite_expr$
let rewrite_alg #f {| eval f |} {| functor f |} 
                  (l:rewrite_t f) (x:f (expr f))
= dflt (In x) <| l.rule (In x)

let rewrite #f {| eval f |} {| functor f |} 
               (l:rewrite_t f) (x:expr f)
= fold_expr (rewrite_alg l) x
//SNIPPET_END: rewrite_expr$

//SNIPPET_START: rewrite_test$
let rewrite_distr
  #f
  {| ev: eval f |} {| functor f |}
  {| leq add f |} {| leq mul f |}
  (pf: squash (ev_add_sem ev /\ ev_mul_sem ev))
  (x:expr f)
: expr f
= rewrite (compose_rewrites (distr_mul_l pf) (distr_mul_r pf)) x

let ex5_l : expr (value ++ add ++ mul) = v 3 *^ (v 1 +^ v 2)
let ex5_r : expr (value ++ add ++ mul) = (v 1 +^ v 2) *^ v 3
let ex6 = ex5_l +^ ex5_r

let ex5'_l : expr (value ++ add ++ mul) = (v 3 *^ v 1) +^ (v 3 *^ v 2)
let ex5'_r : expr (value ++ add ++ mul) = (v 1 *^ v 3) +^ (v 2 *^ v 3)
let ex6' = ex5'_l +^ ex5'_r 

let test56 = assert_norm (rewrite_distr () ex6 == ex6')
//SNIPPET_END: rewrite_test$

//SNIPPET_START: rewrite_soundness$
let rec rewrite_soundness 
    (x:expr (value ++ add ++ mul))
    (l:rewrite_t (value ++ add ++ mul))
: Lemma (eval_expr x == eval_expr (rewrite l x))
= match project #value x with
  | Some (Val _) ->
    l.soundness()
  | _ ->
    match project #add x with
    | Some (Add a b) -> 
      rewrite_soundness a l; rewrite_soundness b l;
      l.soundness()
    | _ ->
      let Some (Mul a b) = project #mul x in
      rewrite_soundness a l; rewrite_soundness b l;
      l.soundness()
//SNIPPET_END: rewrite_soundness$

//SNIPPET_START: rewrite_distr_soundness$
let rewrite_distr_soundness 
    (x:expr (value ++ add ++ mul))
: Lemma (eval_expr x == eval_expr (rewrite_distr () x))
= rewrite_soundness x
    (compose_rewrites (distr_mul_l ()) (distr_mul_r ()))
//SNIPPET_END: rewrite_distr_soundness$
    

module P = FStar.Printf
let rec to_string_specific
    (x:expr (value ++ add ++ mul))
: string
= admit()

// Ex 2:
(* class render (f: [@@@strictly_positive]Type -> Type) = {
  to_string : ... *)