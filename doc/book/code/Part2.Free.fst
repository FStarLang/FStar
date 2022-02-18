module Part2.Free
open FStar.Classical.Sugar

//SNIPPET_START: action_class$
noeq
type action_class = {
  t : Type;
  input_of : t -> Type;
  output_of : t -> Type;
}
//SNIPPET_END: action_class$

//SNIPPET_START: rw_action_class$
type rw =
  | Read
  | Write

let input_of : rw -> Type =
  fun a ->
    match a with
    | Read -> unit
    | Write -> int

let output_of : rw -> Type =
  fun a ->
    match a with
    | Read -> int
    | Write -> unit

let rw_action_class = { t = rw; input_of ; output_of }
//SNIPPET_END: rw_action_class$

//SNIPPET_START: tree$
noeq
type tree (acts:action_class) (a:Type) =
  | Return : x:a -> tree acts a
  | DoThen : act:acts.t ->
             input:acts.input_of act ->
             continue: (acts.output_of act -> tree acts a) ->
             tree acts a
//SNIPPET_END: tree$

//SNIPPET_START: return and bind$
let return #a #acts (x:a)
  : tree acts a
  = Return x

let rec bind #acts #a #b (f: tree acts a) (g: a -> tree acts b)
  : tree acts b
  = match f with
    | Return x -> g x
    | DoThen act i k ->
      DoThen act i (fun x -> bind (k x) g)
//SNIPPET_END: return and bind$

//SNIPPET_START: equiv$
let rec equiv #acts #a (x y: tree acts a) =
  match x, y with 
  | Return vx, Return vy -> vx == vy
  | DoThen actx ix kx, DoThen acty iy ky ->
    actx == acty /\
    ix == iy /\
    (forall o. equiv (kx o) (ky o))
  | _ -> False
//SNIPPET_END: equiv$

//SNIPPET_START: equiv is an equivalence$
let rec equiv_refl #acts #a (x:tree acts a) 
  : Lemma (equiv x x)
  = match x with
    | Return v -> ()
    | DoThen act i k -> 
      introduce forall o. equiv (k o) (k o)
      with (equiv_refl (k o))

let rec equiv_sym #acts #a (x y:tree acts a) 
  : Lemma 
    (requires equiv x y)
    (ensures equiv y x)
  = match x, y with
    | Return _, Return _ -> ()
    | DoThen act i kx, DoThen _ _ ky -> 
      introduce forall o. equiv (ky o) (kx o)
      with equiv_sym (kx o) (ky o)

let rec equiv_trans #acts #a (x y z: tree acts a)
  : Lemma 
    (requires equiv x y /\ equiv y z)
    (ensures equiv x z)
  = match x, y, z with
    | Return _, _, _ -> ()
    | DoThen act i kx, DoThen _ _ ky, DoThen _ _ kz ->
      introduce forall o. equiv (kx o) (kz o)
      with equiv_trans (kx o) (ky o) (kz o)
//SNIPPET_END: equiv is an equivalence$  


//SNIPPET_START: tree is a monad$
let right_identity #acts #a #b (x:a) (g:a -> tree acts b)
  : Lemma (bind (return x) g `equiv` g x)
  = equiv_refl (g x)

let rec left_identity #acts #a (f:tree acts a)
  : Lemma (bind f return `equiv` f)
  = match f with
    | Return _ -> ()
    | DoThen act i k ->
      introduce forall o. bind (k o) return `equiv` (k o)
      with left_identity (k o)

let rec assoc #acts #a #b #c 
              (f1: tree acts a)
              (f2: a -> tree acts b)
              (f3: b -> tree acts c)
  : Lemma (bind f1 (fun x -> bind (f2 x) f3) `equiv`
           bind (bind f1 f2) f3)
  = match f1 with
    | Return v -> 
      right_identity v f2;
      right_identity v (fun x -> bind (f2 x) f3)
    | DoThen act i k ->
      introduce forall o. bind (k o) (fun x -> bind (f2 x) f3) `equiv`
                     bind (bind (k o) f2) f3
      with assoc (k o) f2 f3
//SNIPPET_END: tree is a monad$

//SNIPPET_START: read_and_increment$
let read : tree rw_action_class int = DoThen Read () Return
let write (x:int) : tree rw_action_class unit = DoThen Write x Return
let read_and_increment 
  : tree rw_action_class int
  = x <-- read ;
    write (x + 1);;
    return x
//SNIPPET_END: read_and_increment$

//SNIPPET_START: interp$
let st a = int -> a & int
let rec interp #a (f: tree rw_action_class a)
  : st a 
  = fun s0 -> 
     match f with
     | Return x -> x, s0
     | DoThen Read i k -> 
       interp (k s0) s0
     | DoThen Write s1 k -> 
       interp (k ()) s1
//SNIPPET_END: interp$       

//SNIPPET_START: interp_equiv$       
let feq #a #b (f g: a -> b) = forall x. f x == g x
let rec interp_equiv #a (f g:tree rw_action_class a)
  : Lemma
    (requires equiv f g)
    (ensures feq (interp f) (interp g))
  = match f, g with
    | Return _, Return _ -> ()
    | DoThen act i kf, DoThen _ _ kg ->
      introduce forall o. feq (interp (kf o)) (interp (kg o))
      with interp_equiv (kf o) (kg o)
//SNIPPET_END: interp_equiv$       
