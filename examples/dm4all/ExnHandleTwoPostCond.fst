module ExnHandleTwoPostCond

module List = FStar.List.Tot

let repr (a:Type) = either a exn

let return (a:Type) (x:a) = Inl x

let bind (a : Type) (b : Type) (c : repr a) (f : a -> repr b) =
  match c with
  | Inl x -> f x
  | Inr e -> Inr e

let wp_type (a:Type) = (a -> Type0) -> (exn -> Type0) -> Type0

unfold
let return_wp (a:Type) (x:a) : wp_type a = fun p q -> p x

unfold
let bind_wp (_ : range) (a : Type) (b : Type) (wp : wp_type a) (f : a -> wp_type b) =
  fun p q -> wp (fun x -> f x p q) (fun e -> q e)
  
let interp (a:Type) (c : repr a) : wp_type a = fun p q -> 
  match c with
  | Inl x -> p x
  | Inr e -> q e

total
reifiable
reflectable
new_effect {
  EXC : a:Type -> Effect
  with
       repr      = repr
     ; return    = return
     ; bind      = bind

     ; wp_type   = wp_type
     ; return_wp = return_wp
     ; bind_wp   = bind_wp

     ; interp    = interp
}

val raise : #a:Type0 -> e:exn -> EXC a (fun p q -> q e)
let raise #a e = EXC?.reflect (Inr e)

(* The algebra extension operation is inlined for better readability *)

unfold
let rep_try_catch (#a:Type) 
                  (#b:Type)
                  (c1:repr a)
                  (h_c:exn -> repr b)
                  (c2:a -> repr b) : repr b =
  match c1 with
  | Inl x -> c2 x
  | Inr e -> h_c e

unfold
let wp_return (#a:Type) (x:a) : wp_type a = fun p q -> p x

unfold
let wp_bind (#a:Type) (#b:Type) (wp : wp_type a) (f : a -> wp_type b) =
  fun p q -> wp (fun x -> f x p q) (fun e -> q e)
  
unfold
let wp_raise (#a:Type) (e:exn) : wp_type a = fun p q -> q e

unfold
let wp_try_catch (#a:Type) 
                 (#b:Type) 
                 (wp1:wp_type a) 
                 (h_wp:exn -> wp_type b) 
                 (wp2:a -> wp_type b) : wp_type b = 
  fun p q -> wp1 (fun x -> wp2 x p q) (fun e -> h_wp e p q)

let related #a (r : repr a) (wp : wp_type a) =
  EXC?.stronger _ wp (interp _ r)

(* We should get this from the framework FIXME *)
assume val reify_related (#a #b:Type) (wp:_) (c : (x:a -> EXC b (wp x))) :
                         Lemma (forall (x:a). related (reify (c x)) (wp x))

let lemma_try_catch (#a:Type) 
                    (#b:Type) 
                    (wp1:wp_type a)
                    (c1:either a exn)
                    (h_wp:exn -> wp_type b) 
                    (h_c:(e:exn -> either b exn))
                    (wp2:a -> wp_type b) 
                    (c2:(x:a -> either b exn))
  : Lemma (requires ((related c1 wp1) /\
                     (forall x . related (c2 x) (wp2 x)) /\
                     (forall e . related (h_c e) (h_wp e))))
          (ensures  (forall p q . wp_try_catch wp1 h_wp wp2 p q 
                                  ==>
                                  (match (rep_try_catch c1 h_c c2) with 
                                   | Inl x -> p x
                                   | Inr e -> q e))) =
          (*(ensures  (forall p q . related (rep_try_catch c1 h_c c2) (wp_try_catch wp1 h_wp wp2))) =*)
          (* Logically equivalent to the uncommented ensures, but F*/Z3 below doesn't like it in try_catch below. *)
  match c1 with
  | Inl x -> ()
  | Inr e -> ()

let try_catch (#a:Type) 
              (#b:Type) 
              (#wp1:wp_type a) 
              (c1:unit -> EXC a wp1)
              (#h_wp:exn -> wp_type b) 
              (h_c:(e:exn -> EXC b (h_wp e)))
              (#wp2:a -> wp_type b) 
              (c2:(x:a -> EXC b (wp2 x))) 
            : EXC b (wp_try_catch wp1 h_wp wp2) =
  reify_related (fun _ -> wp1) c1;
  reify_related wp2 c2;
  reify_related h_wp h_c;
  lemma_try_catch #a #b wp1 (reify (c1 ())) h_wp (fun e -> reify (h_c e)) wp2 (fun x -> reify (c2 x));
  EXC?.reflect (rep_try_catch (reify (c1 ())) (fun e -> reify (h_c e)) (fun x -> reify (c2 x)))

let test1 (#a:Type) 
          (#b:Type) 
          (#wp1:wp_type a) 
          (c1:unit -> EXC a wp1)
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXC b (wp2 x))) 
        : EXC b (wp_bind wp1 wp2) =
  try_catch #_ #_ #wp1 c1 #(fun e -> wp_raise e) (fun e -> raise e) #wp2 c2

let test2 (#a:Type) 
          (#b:Type) 
          (v:a)
          (#h_wp:exn -> wp_type b) 
          (h_c:(e:exn -> EXC b (h_wp e)))
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXC b (wp2 x))) 
        : EXC b (wp2 v) = 
  try_catch #_ #_ #(wp_return v) (fun _ -> v) #h_wp h_c #wp2 c2

let test3 (#a:Type) 
          (#b:Type) 
          (e:exn)
          (#h_wp:exn -> wp_type b) 
          (h_c:(e:exn -> EXC b (h_wp e)))
          (#wp2:a -> wp_type b) 
          (c2:(x:a -> EXC b (wp2 x)))
        : EXC b (h_wp e) =
  try_catch #_ #_ #(wp_raise e) (fun _ -> raise e) #h_wp h_c #wp2 c2

assume val div_by_zero_exn : exn

let div_wp (i j:int) = 
  fun p q -> (forall x . j <> 0 /\ x = i / j ==> p x) /\
             (forall e . j = 0 ==> q e)
  
let div (i j:int) 
  : EXC int (div_wp i j) =
  if j = 0 then raise div_by_zero_exn else i / j

let try_div (i j:int)
  : EXC int (fun p q -> forall x . p x) =
  try_catch #_ #_ 
            #(div_wp i j) (fun _ -> div i j) 
            #(fun _ -> wp_return 0) (fun _ -> 0) 
            #(wp_return) (fun x -> x)
