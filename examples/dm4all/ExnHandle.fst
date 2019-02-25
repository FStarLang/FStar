module ExnHandle

module List = FStar.List.Tot

let repr (a:Type) = either a exn

let return (a:Type) (x:a) = Inl x

let bind (a : Type) (b : Type) (c : repr a) (f : a -> repr b) =
  match c with
  | Inl x -> f x
  | Inr e -> Inr e

let wp_type (a:Type) = (either a exn -> Type0) -> Type0

unfold
let return_wp (a:Type) (x:a) : wp_type a = fun p -> p (Inl x)

unfold
let bind_wp (_ : range) (a : Type) (b : Type) (wp : wp_type a) (f : a -> wp_type b) =
  fun p -> wp (fun r -> match r with
                        | Inl x -> f x p
                        | Inr e -> p (Inr e))

let interp (a:Type) (c : repr a) : wp_type a = fun p -> p c

total
reifiable
reflectable
new_effect {
  EXN : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = wp_type
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp    = interp
}

effect Exn (a:Type) (pre:Type0) (post:either a exn -> Type0) =
  EXN a (fun p -> pre /\
          (forall (r:either a exn). post r ==> p r))

val raise : #a:Type0 -> e:exn -> EXN a (fun p -> p (Inr e))
let raise #a e = EXN?.reflect (Inr e)

(* The algebra extension operation is inlined for better readability *)

let handle_rep (#a:Type) 
               (#b:Type)
               (c1:repr a)
               (h_c:exn -> repr b)
               (c2:a -> repr b) : repr b =
  match c1 with
  | Inl x -> c2 x
  | Inr e -> h_c e

unfold
let handle_wp (#a:Type) 
              (#b:Type) 
              (wp1:wp_type a) 
              (h_wp:exn -> wp_type b) 
              (wp2:a -> wp_type b) : wp_type b = 
  fun p -> wp1 (fun r -> match r with
                         | Inl x -> wp2 x p
                         | Inr e -> h_wp e p)

let lemma_handle (#a:Type) 
                 (#b:Type) 
                 (wp1:wp_type a)
                 (c1:either a exn)
                 (h_wp:exn -> wp_type b) 
                 (h_c:(e:exn -> either b exn))
                 (wp2:a -> wp_type b) 
                 (c2:(x:a -> either b exn))
  : Lemma (requires ((forall p . wp1 p ==> p c1) /\
                     (forall p x . wp2 x p ==> p (c2 x)) /\ 
                     (forall p e . h_wp e p ==> p (h_c e))))
          (ensures  (forall p . 
                     wp1 (fun r -> (match r with | Inl x -> wp2 x p | Inr e -> h_wp e p)) 
                     ==>
                     p (match c1 with | Inl x -> c2 x | Inr e -> h_c e))) =
  match c1 with
  | Inl x -> ()
  | Inr e -> ()

let related #a (r : repr a) (wp : wp_type a) =
  EXN?.stronger _ wp (interp _ r)

(* We should get this from the framework FIXME *)
assume val reify_related (#a #b:Type) (wp:_) (c : (x:a -> EXN b (wp x))) :
                         Lemma (forall (x:a). related (reify (c x)) (wp x))

let catch (#a:Type) 
           (#b:Type) 
           (#wp1:wp_type a) 
           (c1:unit -> EXN a wp1)
           (#h_wp:exn -> wp_type b) 
           (h_c:(e:exn -> EXN b (h_wp e)))
           (#wp2:a -> wp_type b) 
           (c2:(x:a -> EXN b (wp2 x))) 
         : EXN b (handle_wp wp1 h_wp wp2) =
  reify_related (fun _ -> wp1) c1;
  reify_related wp2 c2;
  reify_related h_wp h_c;
  lemma_handle wp1 (reify (c1 ())) (h_wp) (fun e -> reify (h_c e)) wp2 (fun x -> reify (c2 x));
  EXN?.reflect (handle_rep (reify (c1 ()) <: either a exn) 
                           (fun e -> reify (h_c e)) 
                           (fun x -> reify (c2 x)))

unfold
let wp_return (#a:Type) (x:a) : wp_type a = fun p -> p (Inl x)

unfold
let wp_bind (#a:Type) (#b:Type) (wp : wp_type a) (f : a -> wp_type b) =
  fun p -> wp (fun r -> match r with
                        | Inl x -> f x p
                        | Inr e -> p (Inr e))

unfold
let wp_raise (#a:Type) (e:exn) : wp_type a = fun p -> p (Inr e)

let test1 (#a:Type) 
          (#b:Type) 
          (#wp1:wp_type a) 
          (c1:unit -> EXN a wp1)
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXN b (wp2 x))) 
        : EXN b (wp_bind wp1 wp2) =
  catch #a #b #wp1 c1 #(fun e -> wp_raise e) (fun e -> raise e) #wp2 c2

let test2 (#a:Type) 
          (#b:Type) 
          (v:a)
          (#h_wp:exn -> wp_type b) 
          (h_c:(e:exn -> EXN b (h_wp e)))
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXN b (wp2 x))) 
        : EXN b (wp2 v) = 
  catch #a #b #(wp_return v) (fun _ -> v) #h_wp h_c #wp2 c2

let test3 (#a:Type) 
          (#b:Type) 
          (e:exn)
          (#h_wp:exn -> wp_type b) 
          (h_c:(e:exn -> EXN b (h_wp e)))
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXN b (wp2 x)))
        : EXN b (h_wp e) =
  catch #a #b #(wp_raise e) (fun _ -> raise e) #h_wp h_c #wp2 c2

assume val div_exn : exn

let div_wp (i j:int) = 
  fun p -> forall x . (match x with
                       | Inl x -> j <> 0 /\ x = i / j
                       | Inr e -> j = 0) 
                      ==> 
                       p x

let div (i j:int) 
  : EXN int (div_wp i j) =
  if j = 0 then raise div_exn else i / j

let try_div (i j:int)
  : EXN int (fun p -> forall x . Inl? x ==> p x) =
  catch #int #int #(div_wp i j) (fun _ -> div i j) #(fun _ p -> p (Inl 0)) (fun _ -> 0) #(wp_return) (fun x -> x)
