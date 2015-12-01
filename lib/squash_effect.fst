
module SquashEffect

total new_effect SQUASH = PURE

(* needed to copy these, why? *)
kind PurePre = Type
kind PurePost (a:Type) = a -> Type
kind PureWP   (a:Type) = PurePost a -> PurePre

effect Squash (a:Type) (pre:PurePre) (post:PurePost a) =
       SQUASH a
           (fun (p:PurePost a) -> pre /\ (forall a. post a ==> p a)) (* WP *)
           (fun (p:PurePost a) -> forall a. pre /\ post a ==> p a)   (* WLP *)

effect Sq (a:Type) =
     SQUASH a (fun (p:PurePost a) -> (forall (x:a). p x))
              (fun (p:PurePost a) -> (forall (x:a). p x))

sub_effect
  PURE ~> SQUASH = fun (a:Type) (wp:PureWP a) (p:PurePost a) -> wp (fun a -> p a)

type squash (p:Type) = (x:unit{p})

assume val unsquash : #p:Type -> squash p -> Sq p

// this correctly fails, squash p and p are not related by subtyping
(* assume val resquash : #p:Type -> #wp:PureWP p -> #wlp:PureWP p -> *)
(*                       (unit -> SQUASH p wp wlp) -> PURE (squash p) wp wlp *)
// wp : (p -> Type) -> Type  not <: ((squash p) -> Type) -> Type

// The post-condition of a Squash is really about the inhabitant,
// but we can't allow that to escape into the non-squash world
assume val resquash : #p:Type -> #pre:PurePre -> #post:PurePost p ->
                      (unit -> Squash p pre post) ->
                      Pure (squash p) (requires pre) (ensures (fun _ -> True))

// less general but much better inference
val resquash' : #p:Type -> (unit -> Sq p) -> Tot (squash p)
let resquash' (p:Type) = resquash #p #True #(fun _ -> True)

// Sanity check: this can encode return_squash and bind_squash

val return_squash : #a:Type -> a -> Tot (squash a)
let return_squash (a:Type) (x:a) = resquash' (fun () -> x)

// CH: currently, F* can prove return_squash directly
// let return_squash (a:Type) (x:a) = ()

val bind_squash : #a:Type -> #b:Type -> squash a -> (a -> Tot (squash b)) ->
  Tot (squash b)
let bind_squash (a:Type) (b:Type) (x:squash a) f =
  resquash' #b (fun _ -> unsquash (f (unsquash x)))


// with this we still can't prove squash_double_arrow
assume val squash_double_arrow : #a:Type -> #p:(a -> Type) ->
  =f:(squash (x:a -> Tot (squash (p x)))) -> Tot (squash (x:a -> Tot (p x)))
// the error bellow is silly though:
// Too many arguments to function of type (#p:Type -> (squash p) -> Sq (p));
// got (unsquash #(x:a -> Tot (squash (p x))) f x)
(* let squash_double_arrow (a:Type) (p:(a -> Type)) *)
(*                         (f:(squash (x:a -> Tot (squash (p x))))) = *)
(*   resquash *)
(*     (fun () -> fun (x:a) -> *)
(*       unsquash #(p x) *)
(*         ((unsquash #(x:a -> Tot (squash (p x))) f) x) *)
(*     ) *)

// if we let bind a bit we get the real problem, result has wrong type
// Expected type "(squash (x:a -> Tot (p x)))";
// got type "(squash (x:a -> SQUASH ((p x))))"
(* let squash_double_arrow (a:Type) (p:(a -> Type)) *)
(*                         (f:(squash (x:a -> Tot (squash (p x))))) = *)
(*   resquash *)
(*     (fun () -> fun (x:a) -> *)
(*       let ff = (unsquash #(x:a -> Tot (squash (p x))) f) in *)
(*       unsquash #(p x) (ff x) *)
(*     ) *)

type ceq (#a:Type) (x:a) : a -> Type =
  | Refl : ceq #a x x

type at_most_one_inhabitant (t : Type) = x:t -> y:t -> Tot (ceq x y)

assume val drop_squash : #p:Type -> at_most_one_inhabitant p -> squash p -> Tot p
