
module Wf

type acc (a:Type) (r:(a -> a -> Type)) (x:a) : Type =
  | AccIntro : (y:a -> r y x -> Tot (acc a r y)) -> acc a r x

type well_founded (a:Type) (r:(a -> a -> Type)) = x:a -> Tot (acc a r x)

val acc_inv : #aa:Type -> #r:(aa -> aa -> Type) -> x:aa -> a:(acc aa r x) ->
              Tot (e:(y:aa -> r y x -> Tot (acc aa r y)){e << a})
let acc_inv x a = match a with | AccIntro h1 -> h1

assume val axiom1_dep : #a:Type -> #b:(a->Type) -> f:(y:a -> Tot (b y)) -> x:a ->
                        Lemma (f x << f)

val axiom1 : #a:Type -> #b:Type -> f:(a -> Tot b) -> x:a ->
             Lemma (Precedes (f x) f)
let axiom1 f x = axiom1_dep f x

val fix_F : #aa:Type -> #r:(aa -> aa -> Type) -> #p:(aa -> Type) ->
            (x:aa -> (y:aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
            x:aa -> a:(acc aa r x) -> Tot (p x) (decreases a)
let rec fix_F (aa:Type) (r:(aa -> aa -> Type)) f x a =
  f x (fun y h -> magic())
(* Unexpected error; please file a bug report, ideally with a
   minimized version of the source program that triggered the error. *)
(* Failure("Bound type variable not found: aa") *)

(* on the other hand this works fine: *)
val fix_F : #aa:Type -> #r:(aa -> aa -> Type) -> #p:(aa -> Type) ->
            (x:aa -> (y:aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
            x:aa -> a:(acc aa r x) -> Tot (p x) (decreases a)
let rec fix_F f x a = f x (fun y h -> magic())
