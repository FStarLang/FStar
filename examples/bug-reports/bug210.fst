module Bug210

(* This is a working version; the problem is that we were forced into this.
   See 210b.fst for what we actually wanted to write. *)

noeq type acc (a:Type) (r:(a -> a -> Type)) (x:a) : Type =
  | AccIntro : (y:a -> r y x -> Tot (acc a r y)) -> acc a r x

(* Working around silly implicit argument stuff in F*,
   can't name these things otherwise in function body
   + putting this just before fix_F also causes lots of troubles
     (see all the commented out admitPs in fix_F;
      even transitivity doesn't work) *)
assume type aa : Type
assume type r : (aa -> aa -> Type)

val acc_inv : x:aa -> a:(acc aa r x) ->
              Tot (e:(y:aa -> r y x -> Tot (acc aa r y)){e << a})
let acc_inv x a = match a with | AccIntro h1 -> h1

assume val axiom1_dep : #a:Type -> #b:(a->Type) -> f:(y:a -> Tot (b y)) -> x:a ->
                        Lemma (f x << f)

val axiom1 : #a:Type -> #b:Type -> f:(a -> Tot b) -> x:a ->
             Lemma (Precedes (f x) f)
let axiom1 f x = axiom1_dep f x

(* Can't prove it is total without axioms: I know that [acc_inv x a << a]
   but from this I cannot deduce [acc_inv x a y h << a] *)
val fix_F : #p:(aa -> Type) ->
            (x:aa -> (y:aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
            x:aa -> a:(acc aa r x) -> Tot (p x) (decreases a)
let rec fix_F f x a =
  f x (fun y h ->
         (* admitP(acc_inv x a << a); (\* should follow from refinement; F* bug *\) *)
         axiom1_dep #aa #(fun y -> r y x -> Tot (acc aa r y)) (acc_inv x a) y;
         (* admitP (acc_inv x a y << acc_inv x a); *)
         axiom1 #(r y x) #(acc aa r y) (acc_inv x a y) h;
         (* admitP (acc_inv x a y h << acc_inv x a y); *)
         (* admitP (acc_inv x a y h << acc_inv x a); *)
         (* admitP (acc_inv x a y h << a); *)
         fix_F f y (acc_inv x a y h)
      )
