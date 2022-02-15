module Part2.Free
open FStar.Classical.Sugar
let state : Type = int

type action =
  | Read
  | Write

let input_of : action -> Type =
  fun a ->
    match a with
    | Read -> unit
    | Write -> state

let output_of : action -> Type =
  fun a ->
    match a with
    | Read -> state
    | Write -> unit

noeq
type m (a:Type) =
  | Return : x:a -> m a
  | DoThen : act:action ->
             input:input_of act ->
             continue: (output_of act -> m a) ->
             m a

let return #a (x:a)
  : m a
  = Return x

let rec bind #a #b (f: m a) (g: a -> m b)
  : m b
  = match f with
    | Return x -> g x
    | DoThen act i k ->
      DoThen act i (fun x -> bind (k x) g)

let rec equiv #a (x y: m a) =
  match x, y with 
  | Return vx, Return vy -> vx == vy
  | DoThen actx ix kx, DoThen acty iy ky ->
    actx == acty /\
    ix == iy /\
    (forall o. equiv (kx o) (ky o))
  | _ -> False

let rec equiv_refl #a (x:m a) 
  : Lemma (equiv x x)
  = match x with
    | Return v -> ()
    | DoThen act i k -> 
      introduce forall o. equiv (k o) (k o)
      with (equiv_refl (k o))

let rec equiv_trans #a (x y z: m a)
  : Lemma 
    (requires equiv x y /\ equiv y z)
    (ensures equiv x z)
  = match x, y, z with
    | Return _, _, _ -> ()
    | DoThen act i kx, DoThen _ _ ky, DoThen _ _ kz ->
      introduce forall o. equiv (kx o) (kz o)
      with equiv_trans (kx o) (ky o) (kz o)
  
let right_identity #a #b (x:a) (g:a -> m b)
  : Lemma (bind (return x) g `equiv` g x)
  = equiv_refl (g x)

let rec left_identity #a (f:m a)
  : Lemma (bind f return `equiv` f)
  = match f with
    | Return _ -> ()
    | DoThen act i k ->
      match act with
      | Write -> left_identity (k ())
      | Read -> 
        introduce forall s. bind (k s) return `equiv` (k s)
        with left_identity (k s)

let rec assoc #a #b #c (f1: m a) (f2: a -> m b) (f3: b -> m c)
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
      
let read : m state = DoThen Read () Return
let write (x:state) : m unit = DoThen Write x Return
let read_and_increment 
  : m int
  = x <-- read ;
    write (x + 1);;
    return x

let st a = state -> a & state
let rec interp #a (f: m a)
  : st a 
  = fun s0 -> 
     match f with
     | Return x -> x, s0
     | DoThen Read i k -> 
       interp (k s0) s0
     | DoThen Write s1 k -> 
       interp (k ()) s1
       
