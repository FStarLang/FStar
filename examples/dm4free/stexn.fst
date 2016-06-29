module StExn
let pre = int -> Type0
let post (a:Type) = (option a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0
inline let return_wp (a:Type) (x:a) (n0:int) (post:post a) = 
  forall y. y=(Some x, n0) ==> post y

//working around #517 by adding an explicit 'val'
inline val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (function 
	| (None, n1) -> post (None, n1)
	| (Some x, n1) -> g x n1 post)

inline let if_then_else  (a:Type) (p:Type)
                            (wp_then:wp a) (wp_else:wp a)
                            (h0:int) (post:post a) =
     l_ITE p
        (wp_then h0 post)
	(wp_else h0 post)
inline let ite_wp        (a:Type)
                            (wp:wp a)
                            (h0:int) (post:post a) =
  wp h0 post
inline let stronger  (a:Type) (wp1:wp a) (wp2:wp a) =
     (forall (p:post a) (h:int). wp1 h p ==> wp2 h p)

inline let close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (wp a)))
                            (h:int) (p:post a) =
     (forall (b:b). wp b h p)
inline let assert_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p /\ wp h q
inline let assume_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p ==> wp h q
inline let null_wp       (a:Type)
                            (h:int) (p:post a) =
     (forall (x:option a) (h:int). p (x,h))
inline let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (option a * int) (wp n0)

inline val bind: (a:Type) -> (b:Type) -> (wp0:wp a) -> (wp1:(a -> Tot (wp b))) 
		 -> (f:repr a wp0)
		 -> (g:(x:a -> Tot (repr b (wp1 x)))) 
		 -> Tot (repr b (bind_wp range_0 a b wp0 wp1))
let bind a b wp0 wp1 f g  
  = fun n0 -> admit(); match f n0 with 
		    | None, n1 -> None, n1
		    | Some x, n1 -> g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> (Some x, n0)

let get (u:unit) : repr int (fun n0 post -> post (Some n0, n0))
  = fun n0 -> Some n0, n0

let put (n:int) : repr unit (fun n0 post -> post (Some (), n))
  = fun x -> Some (), n

//this counts the number of exceptions that are raised
val raise : a:Type0 -> Tot (repr a (fun h0 (p:post a) -> p (None, h0 + 1)))
let raise a (h:int) = None, h + 1

//no reflect, to preserve the 'raise' abstraction
reifiable new_effect {
  StateExn : a:Type -> wp:wp a -> Effect
  with //repr is new; it's the reprentation of ST as a value type
       repr         = repr
       //bind_wp is exactly as it is currently
       //produced by the *-translation of bind above
     ; bind_wp      = bind_wp
       //bind is new, it is the elaboration of the bind above
     ; bind         = bind
      //return_wp is a renaming of the current return, it is the *-translation of the return above
     ; return_wp    = return_wp
      //return is new; it is the elaboration of the return above
     ; return       = return
     //the remaining are just as what we have now
     ; if_then_else = if_then_else
     ; ite_wp       = ite_wp
     ; stronger     = stronger
     ; close_wp     = close_wp
     ; assert_p     = assert_p
     ; assume_p     = assume_p
     ; null_wp      = null_wp
     ; trivial      = trivial
  and effect_actions
    //these are new
      get  = get
    ; put  = put
    ; raise = raise
}

inline let lift_pure_stexn (a:Type) (wp:pure_wp a) (h0:int) (p:post a) = wp (fun a -> p (Some a, h0))
sub_effect PURE ~> StateExn = lift_pure_stexn

effect StExn (a:Type) (req:pre) (ens:int -> option a -> int -> GTot Type0) =
       StateExn a
         (fun (h0:int) (p:post a) -> req h0 /\ (forall (r:option a) (h1:int). (req h0 /\ ens h0 r h1) ==> p (r, h1))) (* WP *)

effect S (a:Type) = 
       StateExn a (fun h0 p -> forall x. p x)

//let f = StateExn.reflect (fun h0 -> None, h0); this rightfully fails, since StateExn is not reflectable
val div_intrinsic : i:nat -> j:int -> StExn int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> match x with 
			| None -> h0 + 1 = h1 /\ j=0 
			| Some z -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0 then StateExn.raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
  if j=0 then StateExn.raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) 0 with
         | None, 1 -> j = 0
	 | Some z, 0 -> j <> 0 /\ z = i / j) = ()
