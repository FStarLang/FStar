module Bug844

open FStar.Constructive
open FStar.Squash

assume val excluded_middle_squash : p:Type0 -> GTot (p \/ ~p)

assume type pow (p:Type)

noeq type retract 'a 'b : Type =
  | MkR: i:('a -> GTot 'b) ->
         j:('b -> GTot 'a) ->
         inv:(x:'a -> GTot (ceq (j (i x)) x)) ->
         retract 'a 'b

noeq type retract_cond 'a 'b : Type =
  | MkC: i2:('a -> GTot 'b) ->
         j2:('b -> GTot 'a) ->
         inv2:(retract 'a 'b -> x:'a -> GTot (ceq (j2 (i2 x)) x)) ->
         retract_cond 'a 'b

val l1: (a:Type0) -> (b:Type0) -> GTot (squash (retract_cond (pow a) (pow b)))
let l1 (a:Type) (b:Type) =
   bind_squash (excluded_middle_squash (retract (pow a) (pow b)))
	      (fun (x:c_or (retract (pow a) (pow b)) (~ (retract (pow a) (pow b)))) ->
	         match x with
		 | Left (MkR f0 g0 e) ->
		   return_squash (MkC f0 g0 (fun _ -> e) (* <- this lambda causes the problem *))
		 | Right nr ->
                   magic())
