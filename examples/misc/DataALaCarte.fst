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
module DataALaCarte
open FStar.Tactics.Typeclasses
#set-options "--z3rlimit_factor 4 --z3cliopt 'smt.qi.eager_threshold=100' --fuel 2 --ifuel 2"
(**
 * This module is an adaptation of S. Swierstra's Data Type a la Carte
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

noeq
type expr (f : ([@@@strictly_positive]Type -> Type)) =
  | In of (f (expr f))

noeq
type coprod (f g: ([@@@strictly_positive]Type -> Type)) ([@@@strictly_positive]a:Type) =
  | Inl of f a
  | Inr of g a

type value ([@@@strictly_positive]a:Type) =
  | Val of int

type add ([@@@strictly_positive]a:Type) =
  | Add : a -> a -> add a

let ( ** ) (f g: ([@@@strictly_positive]Type -> Type)) = coprod f g

let addExample : expr (value ** add) = In (Inr (Add (In (Inl (Val 118))) (In (Inl (Val 1219)))))

class functor (f:[@@@strictly_positive]Type -> Type) = {
  fmap : (#a:Type -> #b:Type -> x:f a -> (y:a{y << x} -> b) -> f b)
}

instance functor_value : functor value =
  let fmap (#a #b:Type) (x:value a) (f:(y:a{y<<x} -> b)) : value b =
    let Val x = x in
    Val x
  in
  { fmap }

instance functor_add : functor add =
  let fmap (#a #b:Type) (x:add a) (f:(y:a{y<<x} -> b)) : add b =
    match x with
    | Add x y ->
      let x' = f x in
      let y' = f y in
      Add x' y'
  in
  { fmap }

instance functor_coprod (f g:([@@@strictly_positive]Type -> Type)) {| ff: functor f |} {| fg: functor g |}
: functor (coprod f g)
= let fmap (#a #b:Type) (x:coprod f g a) (a2b:(y:a{y << x} -> b)) 
  : coprod f g b
  = match x with
    | Inl x -> Inl (ff.fmap x a2b)
    | Inr x -> Inr (fg.fmap x a2b)
  in
  { fmap }


let rec fold_expr
    (#f:([@@@strictly_positive]Type -> Type))
    {| ff: functor f |}
    (#a:Type)
    (alg:f a -> a)
    (e:expr f)
: a
= let In t = e in
  alg (ff.fmap t (fun (x:expr f { x << e }) -> fold_expr alg x))

[@@fundeps[2]]
class eval (f: [@@@strictly_positive]Type -> Type) (a:Type) = {
  evalAlg : f a -> a
}

instance eval_val : eval value int =
  let evalAlg : value int -> int = fun (Val x) -> x in
  { evalAlg }

instance eval_add : eval add int =
  let evalAlg : add int -> int = fun (Add x y) -> x + y in
  { evalAlg }

instance eval_coprod 
    (f g: ([@@@strictly_positive]Type -> Type)) (a:Type)
    {| ef: eval f a |}
    {| eg: eval g a |} 
: eval (coprod f g) a
= let evalAlg (x:coprod f g a) : a =
    match x with
    | Inl x -> ef.evalAlg x
    | Inr y -> eg.evalAlg y
  in
  { evalAlg }

let eval_expr 
  (#a:Type)
  (#f:([@@@strictly_positive]Type -> Type))
  {| ef: eval f a |} {| functor f |} (x:expr f)
: a = fold_expr ef.evalAlg x

let test = assert_norm (eval_expr addExample == 1337)

type mul ([@@@strictly_positive]a:Type) =
  | Mul : a -> a -> mul a

open FStar.Mul
instance functor_mul : functor mul = 
  let fmap (#a #b:Type) (x:mul a) (f:(y:a{y<<x} -> b)) : mul b =
    let Mul x y = x in
    Mul (f x) (f y)
  in
  { fmap }

instance eval_mul : eval mul int =
  let evalAlg : mul int -> int = fun (Mul x y) -> x * y in
  {  evalAlg }

let inj_t (f g:Type -> Type) = #a:Type -> f a -> g a
let proj_t (f g:Type -> Type) = #a:Type -> x:g a -> option (f a)
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

instance leq_id f : leq f f = {
  inj=(fun #_ x -> x);
  proj=(fun #_ x -> Some x);
  inversion=(fun _ -> ())
}

instance leq_ext_left (f g:[@@@strictly_positive]Type -> Type) : leq f (g ** f) = 
let inj : inj_t f (g ** f) = Inr in 
let proj : proj_t f (g ** f) = fun #a x ->
  match x with
  | Inl _ -> None
  | Inr x -> Some x
in
{ inj; proj; inversion=(fun _ -> ()) }

let compose (#a #b #c:Type) (f:b -> c) (g: a -> b) (x:a) : c = f (g x)

instance leq_cong_left 
  (f g h:[@@@strictly_positive]Type -> Type)
  {| f_inj:leq f h |}
: leq f (h ** g)
= let inj : inj_t f (h ** g) = fun #a x -> Inl (f_inj.inj x) in
  let proj : proj_t f (h ** g) = fun #a x -> 
    match x with
    | Inl x -> f_inj.proj x
    | _ -> None
  in
  { inj; proj; inversion=(fun _ -> f_inj.inversion()) }

let inject (#f #g:([@@@strictly_positive]Type -> Type)) {| gf: leq g f |}
: g (expr f) -> expr f 
= compose In gf.inj

let project  (#g #f:([@@@strictly_positive]Type -> Type)) {| gf: leq g f |}
: x:expr f -> option (g (expr f)) 
= fun (In x) -> gf.proj x

let inject_project 
  (#f #g:([@@@strictly_positive]Type -> Type)) {| gf: leq g f |}
  (x:expr f)
: Lemma (
    match project #g #f x with
    | Some y -> inject #f #g  y == x
    | _ -> True
) [SMTPat (project #g #f x)]
= gf.inversion()

let project_inject (#f #g:_) {| gf: leq g f |} (x:g (expr f))
: Lemma (
    project #g #f (inject #f #g x) == Some x
) [SMTPat (project #g #f (inject #f #g x))]
= gf.inversion()

let v #f {| vf: leq value f |} (x:int)
: expr f
= inject (Val x)

let ( +^ ) #f {| vf : leq add f |} (x y: expr f)
: expr f
= inject (Add x y)

let ( *^ ) #f {| vf : leq mul f |} (x y: expr f)
: expr f
= inject (Mul x y)

let ex2 : expr (value ** add ** mul) = v 1001 +^ v 1833 +^ v 13713 *^ v 24
let test2 = assert_norm (eval_expr ex2 == ((1001 + 1833 + 13713 * 24)))

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
let ex3 : expr (value ** add ** mul) = lift addExample *^ v 2
let test3 = assert_norm (eval_expr ex3 == (1337 * 2))

class render (f: [@@@strictly_positive]Type -> Type) = {
  to_string : 
    #g:_ ->
    x:f (expr g) ->
    (y:g (expr g) { y << x } -> string) ->
    string
}

instance render_value : render value =
  let to_string #g (x:value (expr g)) _ : string =
    match x with
    | Val x -> string_of_int x
  in
  { to_string }


instance render_add : render add =
  let to_string #g (x:add (expr g)) (to_str0: (y:g (expr g) {y << x} -> string)) : string =
    match x with
    | Add x y ->
      let In x = x in
      let In y = y in
      "(" ^ to_str0 x ^ " + " ^ to_str0 y ^ ")"
  in
  { to_string }

instance render_mul : render mul =
  let to_string #g (x:mul (expr g)) (to_str0: (y:g (expr g) {y << x} -> string)) : string =
    match x with
    | Mul x y ->
      let In x = x in
      let In y = y in
      "(" ^ to_str0 x ^ " * " ^ to_str0 y ^ ")"
  in
  { to_string }

instance render_coprod (f g: _)
  {| rf: render f |} 
  {| rg: render g |}
: render (coprod f g)
= let to_string #h (x:coprod f g (expr h)) (rc: (y:h (expr h) { y << x }) -> string): string =
    match x with
    | Inl x -> rf.to_string #h x rc
    | Inr y -> rg.to_string #h y rc
  in
  { to_string }

let rec render0_render
    (#f: _)
    {| rf: render f |}
    (x: f (expr f))
: string
= rf.to_string #f x render0_render

let pretty #f (e:expr f) {| rf: render f |} : string =
  let In e = e in
  rf.to_string e render0_render

let test4 = pretty ex3
let tt = assert_norm (pretty ex3 == "((118 + 1219) * 2)")

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

let rewrite_rule f = expr f -> option (expr f)
let rewrite_rule_soundness #f (r:rewrite_rule f)
  {| eval f int |} {| functor f |} 
  (x:expr f) =
    match r x with
    | None -> True
    | Some y -> eval_expr #int x == eval_expr #int y
  
noeq
type rewrite_t (f:_) {| eval f int |} {| functor f |} = {
  rule: rewrite_rule f;
  soundness: unit -> Lemma (forall x. rewrite_rule_soundness rule x)
}

let or_else (x:option 'a)
           (or_else: squash (None? x) -> 'a)
: 'a
= match x with
  | None -> or_else ()
  | Some y -> y

let ev_val_sem #f (ev: eval f int) {| functor f |} {| leq value f |} =
  forall (x:expr f). dflt True 
    (let? Val a= project x in
     Some #prop (eval_expr x == a))

let ev_add_sem #f (ev: eval f int) {| functor f |} {| leq add f |} =
  forall (x:expr f). dflt True 
    (let? Add a b = project x in
     Some #prop (eval_expr x == eval_expr a + eval_expr b))

let ev_mul_sem #f (ev: eval f int) {| functor f |} {| leq mul f |} =
  forall (x:expr f). dflt True 
    (let? Mul a b = project x in
     Some #prop (eval_expr x == eval_expr a * eval_expr b))

let distr_mul_l #f
    {| ev: eval f int |} {| functor f |}
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
    {| ev: eval f int |} {| functor f |}
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

let compose_rewrites #f
    {| ev: eval f int |} {| functor f |}
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

let rewrite_alg #f {| eval f int |} {| functor f |} 
                  (l:rewrite_t f) (x:f (expr f))
= dflt (In x) <| l.rule (In x)

let rewrite #f {| eval f int |} {| functor f |} 
               (l:rewrite_t f) (x:expr f)
= fold_expr (rewrite_alg l) x

let rewrite_distr
  #f
  {| ev: eval f int |} {| functor f |}
  {| leq add f |} {| leq mul f |}
  (pf: squash (ev_add_sem ev /\ ev_mul_sem ev))
  (x:expr f)
: expr f
= rewrite (compose_rewrites (distr_mul_l pf) (distr_mul_r pf)) x

let rec rewrite_soundness 
    (x:expr (value ** add ** mul))
    (l:rewrite_t (value ** add ** mul))
: Lemma (eval_expr #int x == eval_expr (rewrite l x))
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


let ex5_l : expr (value ** add ** mul) = v 3 *^ (v 1 +^ v 2)
let ex5_r : expr (value ** add ** mul) = (v 1 +^ v 2) *^ v 3
let ex6 = ex5_l +^ ex5_r

let ex5'_l : expr (value ** add ** mul) =
  (v 3 *^ v 1) +^ (v 3 *^ v 2)
let ex5'_r : expr (value ** add ** mul) =
  (v 1 *^ v 3) +^ (v 2 *^ v 3)
let ex6' = ex5'_l +^ ex5'_r 

module T = FStar.Tactics.V2
let test56 = 
 assert (rewrite_distr () ex6 == ex6')
    by (T.compute())

module P = FStar.Printf
let rec to_string_alt 
    (x:expr (value ** add ** mul))
: string
= (let? Val x = project #value x in return <| string_of_int x) 
  `or_else` fun _ ->
  (let? Add x y = project #add x in 
   return <| P.sprintf "(%s + %s)" (to_string_alt x) (to_string_alt y))
  `or_else` fun _ ->
  let Some (Mul x y) = project #mul x in
  P.sprintf "(%s * %s)" (to_string_alt x) (to_string_alt y)

let prj #g #f {| gf: leq g f |} (#a:Type) (x:f a)
: option (g a)
= gf.proj x

let has_add_alg (x: (value ** add ** mul) bool) 
: bool
= (let? _ = prj #value x in return false) 
  `or_else` fun _ -> 
  (let? _ = prj #add x in return true)
  `or_else` fun _ -> 
  (let Some (Mul x y) = prj #mul x in x || y)

let has_add 
  (x:expr (value ** add ** mul))
: bool
= fold_expr has_add_alg x