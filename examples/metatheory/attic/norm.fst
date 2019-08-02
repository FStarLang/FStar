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
module Norm

open Prims
open Stlc

(* Ideas for trying to fix the logical reasoning mess:
0. Improve our type-checker to the point it can do the right inference?
   It's unclear to me whether that's possible or even desirable.
1. Stop using Lemma, use refinements instead since those
   might make inference for _intro and _elim things easier.
2. Give a constructive/inductive interpretation to logical
   connectives like /\, \/, Exists ... *)

(* Reflexive-transitive closure of step *)

kind Relation (a:Type) = a -> a -> Type

(* CH: needed to unfold the definition of Relation to make this work;
   for failed attempts to define this see below *)
type multi (a:Type) (r:(a -> a -> Type)) : a -> a -> Type =
  | Multi_refl : x:a -> multi a r x x
  | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z

(* CH: without "logic" qualifier the definition above is useless for Z3,
   doing encoding by hand for now *)
assume val emulti_refl : (forall (a:Type) (r:Relation a) (x:a). multi a r x x)
assume val emulti_step : (forall (a:Type) (r:Relation a) (x:a) (y:a) (z:a).
  r x y ==> multi a r y z ==> multi a r x z)
assume val emulti_inv : (forall (a:Type) (r:Relation a) (x:a) (z:a).
  multi a r x z ==> (x = z \/ (exists (y:a). r x y /\ multi a r y z)))
assume val emulti_ind : (forall (a:Type) (r:Relation a) (p:Relation a).
  (forall (x:a). p x x) ==>
  (forall (x:a) (y:a) (z:a). r x y ==> multi a r y z ==> p y z ==> p x z) ==>
  (forall (x:a) (y:a). multi a r x y ==> p x y))

(* CH: Another encoding, produces lemmas instead of formulas, this
   allows these things to be used both manually and automatically
   (once we have `using` at least). Especially for things like induction,
   manual instantiation is the more realistic option. *)
assume val multi_refl : a:Type -> r:Relation a -> x:a -> Lemma (multi a r x x)
assume val multi_step : a:Type -> r:Relation a -> x:a -> y:a -> z:a -> Lemma
      (requires (r x y /\ multi a r y z))
      (ensures (multi a r x z))
assume val multi_inv : a:Type -> r:Relation a -> x:a -> z:a -> Lemma
      (requires (multi a r x z))
      (ensures (x = z \/ (exists (y:a). r x y /\ multi a r y z)))
assume val multi_ind : a:Type -> r:Relation a -> p:Relation a ->
      (x:a -> Tot (p x x)) ->
      (x:a -> y:a -> z:a{r x y /\ multi a r y z /\ p y z} -> Tot (p x z)) ->
      x:a -> y:a -> Lemma (requires (multi a r x y)) (ensures (p x y))
(* let rec multi_ind (a:Type) (r:Relation a) (p:Relation a) h1 h2 x y = ()
   don't have anything to recurse over, multi a r x y is not proper argument *)

(* This still fails, see https://github.com/FStarLang/FStar/issues/96
val multi_ind_provable : a:Type -> r:Relation a -> p:Relation a ->
      (x:a -> Lemma (p x x)) ->
      (x:a -> y:a -> z:a{r x y /\ p y z} -> multi a r y z -> Lemma (p x z)) ->
      x:a -> y:a -> multi a r x y -> Lemma (p x y)
let rec multi_ind_provable (a:Type) (r:Relation a) (p:Relation a) h1 h2 x y h =
  match h with
  | Multi_refl x' -> h1 x'
  | Multi_step x' y' z' hr hm ->
      h2 x' y' z' (multi_ind_provable a r p h1 h2 y' z' hm)
*)

(*
Kinds "(_:a -> _:a -> Type)" and "Type" are incompatible

type multi (a:Type) (r:Relation a) : Relation a =
  | Multi_refl : x:a -> multi a r x x
  | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z

same error below (non-uniform args):
Kinds "(_:'a -> _:'a -> Type)" and "Type" are incompatible

type multi : 'a:Type -> ('a -> 'a -> Type) -> 'a -> 'a -> Type =
  | Multi_refl : x:'a -> r:('a -> 'a -> Type) -> multi r x x
  | Multi_step : x:'a -> y:'a -> z:'a -> r:('a -> 'a -> Type) -> r x y -> multi r y z -> multi r x z
*)

type step_rel (e:exp) (e':exp) : Type = step e == Some e'

type steps : exp -> exp -> Type = multi exp step_rel

type halts (e:exp) : Type = (exists (e':exp). (steps e e' /\ is_value e'))

val value_halts : v:exp ->
  Lemma (requires (is_value v))
        (ensures (halts v))
let value_halts v =
  multi_refl exp step_rel v

(* This has a negative occurrence of R that makes Coq succumb,
   although this definition is just fine (the type decreases);
   F* should have similar problems as soon as we start checking
   for negative occurrences. *)
type red : ty -> exp -> Type =
  | R_bool : e:exp{typing empty e = Some TBool /\ halts e} -> red TBool e
  | R_arrow : t1:ty -> t2:ty
               -> e:exp{typing empty e = Some (TArrow t1 t2) /\ halts e}
               -> (e':exp -> red t1 e' -> Tot (red t2 (EApp e e')))
               -> red (TArrow t1 t2) e
  | R_pair : t1:ty -> t2:ty
               -> e:exp{typing empty e = Some (TPair t1 t2) /\ halts e}
               -> red t1 (EFst e)
               -> red t2 (ESnd e)
               -> red (TPair t1 t2) e

assume val r_bool : e:exp -> Lemma
  (requires (typing empty e = Some TBool /\ halts e))
  (ensures (red TBool e))
assume val r_arrow : t1:ty -> t2:ty ->
  e:exp{forall (e':exp). red t1 e' ==> red t2 (EApp e e')} -> Lemma
  (requires (typing empty e = Some (TArrow t1 t2) /\ halts e))
  (ensures (red (TArrow t1 t2) e))
assume val r_pair : t1:ty -> t2:ty -> e:exp -> Lemma
  (requires (typing empty e = Some (TPair t1 t2) /\ halts e
             /\ red t1 (EFst e) /\ red t2 (ESnd e)))
  (ensures (red (TPair t1 t2) e))
(* CH: might want to still get rid of the existentials *)
assume val red_inv : t:ty -> e:exp -> Lemma
  (requires (red t e))
  (ensures (typing empty e = Some t /\ halts e /\
             (t = TBool \/
             (exists (t1:ty) (t2:ty). t = TArrow t1 t2 /\
               (forall (e':exp). red t1 e' ==> red t2 (EApp e e')) \/
             (exists (t1:ty) (t2:ty). t = TPair t1 t2 /\
               red t1 (EFst e) /\ red t2 (ESnd e))))))
(* The converse direction is provable from r_bool, r_arrow, and r_pair *)
val red_fwd : t:ty -> e:exp -> Lemma
  (requires (typing empty e = Some t /\ halts e /\
             (t = TBool \/
             (exists (t1:ty) (t2:ty). t = TArrow t1 t2 /\
               (forall (e':exp). red t1 e' ==> red t2 (EApp e e')) \/
             (exists (t1:ty) (t2:ty). t = TPair t1 t2 /\
               red t1 (EFst e) /\ red t2 (ESnd e))))))
  (ensures (red t e))
let red_fwd t e =
  match t with
  | TBool -> r_bool e
  | TArrow t1 t2 -> r_arrow t1 t2 e
  | TPair t1 t2 -> r_pair t1 t2 e

(* My original attempt -- red' called recursively only in refinement *)
type red' : ty -> exp -> Type =
  | R_bool' : e:exp{typing empty e = Some TBool /\ halts e} -> red' TBool e
  | R_arrow' : e:exp -> t1:ty -> t2:ty{typing empty e = Some (TArrow t1 t2)
      /\ halts e /\ (forall (e':exp). red' t1 e' ==> red' t2 (EApp e e'))} ->
      red' (TArrow t1 t2) e

(* In Coq we define R/red by recursion on the type,
   we don't have fixpoints in Type in F* though (see mailing list discussion)
The type of R is
val R : ty -> exp -> Type
*)
(*
Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | TBool  => True
   | TArrow T1 T2 => (forall s, R T1 s -> R T2 (tapp t s))
   | TProd T1 T2 => (R T1 (tfst t)) /\ (R T2 (tsnd t))
   end).
*)

val red_halts : t:ty -> e:exp -> Lemma
  (requires (red t e))
  (ensures (halts e))
let red_halts t e = red_inv t e

val red_typing : t:ty -> e:exp -> Lemma
  (requires (red t e))
  (ensures (typing empty e = Some t))
let red_typing t e = red_inv t e

(* CH: we need to make pre, post, and maybe also a implicit;
   without that this is a complete pain to use;
   unfortunately F* can't properly infer these things currently *)
(* CH: I would also write the {exists (x:a). p x} refinement directly
   on f instead of adding a spurious unit, unfortunately that causes
   a bogus error *)
assume val exists_elim :
  #pre:Type -> #post:(unit->Type) -> #a:Type -> p:(a->Type) ->
  u:unit{exists (x:a). p x} -> f:(x:a{p x} -> Pure unit pre post) ->
  Pure unit pre post

val exists_intro: #a:Type -> p:(a -> Type) ->
    x:a{p x} -> Tot (u':unit{exists (x:a). p x})
let exists_intro (a:Type) (p:(a->Type)) x = ()

val step_preserves_halting_ltr : e:exp -> e':exp -> Lemma
  (requires (step e = Some e' /\ halts e))
  (ensures (halts e'))
let step_preserves_halting_ltr e e' =
  exists_elim #(step e = Some e' /\ halts e) #(fun _ -> halts e') #exp
  (fun (eh:exp) -> steps e eh /\ is_value eh) ()
  (fun eh -> multi_inv exp step_rel e eh)

val step_preserves_halting_rtl : e:exp -> e':exp -> Lemma
  (requires (step_rel e e' /\ halts e'))
  (ensures (halts e))
let step_preserves_halting_rtl e e' =
  exists_elim #(step_rel e e' /\ halts e') #(fun _ -> halts e) #exp
  (fun (eh:exp) -> steps e' eh /\ is_value eh) ()
  (fun eh -> multi_step exp step_rel e e' eh)
(* ; exists_intro exp (fun eh -> steps e eh /\ is_value eh) eh
   -- not required, F* can figure this out *)

assume val impl_intro : #pre:Type -> #p1:Type -> #p2:Type ->
  (unit -> Pure unit (pre/\p1) (fun _ -> p2)) ->
  Pure unit pre (fun _ -> p1 ==> p2)

(* F* can't infer pre, p1, and p2 (see iff_intro below) *)
val iff_split : #pre:Type -> #p1:Type -> #p2:Type ->
  (unit -> Pure unit pre (fun _ -> p1 ==> p2)) ->
  (unit -> Pure unit pre (fun _ -> p2 ==> p1)) ->
  Pure unit pre (fun _ -> p1 <==> p2)
let iff_split u1 u2 = u1(); u2()

(* F* can't infer pre, p1, and p2 (see step_preserves_halting below) *)
val iff_intro : #pre:Type -> #p1:Type -> #p2:Type ->
  (unit -> Pure unit (pre/\p1) (fun _ -> p2)) ->
  (unit -> Pure unit (pre/\p2) (fun _ -> p1)) ->
  Pure unit pre (fun _ -> p1 <==> p2)
let iff_intro (pre:Type) (p1:Type) (p2:Type) u1 u2 =
  iff_split #pre #p1 #p2 (fun () -> impl_intro u1) (fun () -> impl_intro u2)

(* One more variant, still no inference
assume val impl_intro : #pre:Type -> #p1:Type -> #p2:Type ->
  (u:unit{p1} -> Pure unit pre (fun _ -> p2)) ->
  Pure unit pre (fun _ -> p1 ==> p2)

(* F* can't infer pre, p1, and p2 (see step_preserves_halting below) *)
val iff_intro : #pre:Type -> #p1:Type -> #p2:Type ->
  (u:unit{p1} -> Pure unit pre (fun _ -> p2)) ->
  (u:unit{p2} -> Pure unit pre (fun _ -> p1)) ->
  Pure unit pre (fun _ -> p1 <==> p2)
let iff_intro (pre:Type) (p1:Type) (p2:Type) u1 u2 =
  iff_split #pre #p1 #p2
    (fun () -> impl_intro #pre #p1 #p2 u1)
    (fun () -> impl_intro #pre #p2 #p1 u2)
*)

val step_preserves_halting : e:exp -> e':exp -> Lemma
  (requires (step e = Some e'))
  (ensures (halts e <==> halts e'))
let step_preserves_halting e e' =
  iff_intro #(b2t (step e = Some e')) #(halts e) #(halts e')
    (fun () -> step_preserves_halting_ltr e e')
    (fun () -> step_preserves_halting_rtl e e')

(* this seems reasonable, not provable?
   also pre and post not properly inferred *)
assume val real_cut : #pre:Type -> #post:Type -> p:Type ->
  (unit -> Tot unit p) ->
  (unit -> Pure unit (pre/\p) (fun _ -> post)) ->
  Pure unit pre (fun _ -> post)
(* let real_cut (pre:Type) (post:Type) (p:Type) h1 h2 = h1(); h2() -- this fails *)

assume val forall_intro : #a:Type -> #p:(a -> Type) ->
  (x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)

assume val impl_intro' : #p1:Type -> #p2:Type ->
  (u:unit{p1} -> Lemma (ensures p2)) ->
  Lemma (p1 ==> p2)

val step_preserves_R : e:exp -> e':exp -> t:ty -> Lemma
  (requires (step e = Some e' /\ red t e))
  (ensures (red t e'))
  (decreases t)
let rec step_preserves_R e e' t =
  red_inv t e;
  preservation e;
  step_preserves_halting e e';
  (match t with
  | TBool -> r_bool e'
  | TArrow t1 t2 ->
     real_cut #(step e = Some e' /\ red t e) #(red t e')
       (forall (e'':exp). red t1 e'' ==> red t2 (EApp e' e''))
       (fun _ -> forall_intro #exp #(fun e'' -> red t1 e'' ==> red t2 (EApp e' e''))
                 (fun e'' -> impl_intro' #(red t1 e'') #(red t2 (EApp e' e''))
                   (fun _ -> step_preserves_R (EApp e e'') (EApp e' e'') t2)))
       (fun _ -> r_arrow t1 t2 e')
  | TPair t1 t2 ->
      step_preserves_R (EFst e) (EFst e') t1;
      step_preserves_R (ESnd e) (ESnd e') t2;
      r_pair t1 t2 e' )
