module RBTree

type color =
  | R
  | B

type rbtree =
  | E
  | T: col:color -> left:rbtree -> key:nat -> right:rbtree -> rbtree


val color_of: t:rbtree -> Tot color
let color_of t = match t with
  | E -> B
  | T c _ _ _ -> c

val black_height: t:rbtree -> Tot (option nat)
let rec black_height t = match t with
  | E -> Some 0
  | T c a _ b -> 
    let hha = black_height a in
    let hhb = black_height b in
    match (hha, hhb) with
      | Some ha, Some hb ->
	if ha = hb then
	  if c = R then Some ha else Some (ha + 1)
	else
	  None
      | _, _ -> None

val h_inv: t:rbtree -> Tot bool
let h_inv t = is_Some (black_height t)

val c_inv: t:rbtree -> Tot bool
let rec c_inv t = match t with
  | E -> true
  | T R a _ b -> color_of a = B && color_of b = B && c_inv a && c_inv b
  | T B a _ b -> c_inv a && c_inv b

type r_inv (t:rbtree) = is_E t \/ (is_T t /\ T.col t = B)

val key_order: t:rbtree -> Tot bool
let rec key_order t = match t with
  | E -> true
  | T _ a x b ->
    let a_ok = match a with
      | E -> true
      | T _ _ y _ -> x > y
    in
    let b_ok = match b with
      | E -> true
      | T _ _ y _ -> y > x
    in
    key_order a && key_order b && a_ok && b_ok


type balanced_rbtree (t:rbtree) = r_inv t /\ h_inv t /\ c_inv t


type not_c_inv (t:rbtree) =
   (T.col t = R /\ T.col (T.left t) = R) \/
   (T.col t = R /\ T.col (T.right t) = R)

type lr_c_inv (t:rbtree) = c_inv (T.left t) /\ c_inv (T.right t)

type pre_balance (c:color) (lt:rbtree) (rt:rbtree) =
    (h_inv lt /\ h_inv rt /\ Some.v (black_height lt) = Some.v (black_height rt))

    /\

    ((c = B /\ not_c_inv lt /\ lr_c_inv lt /\ c_inv rt) \/
    (c = B /\ not_c_inv rt /\ lr_c_inv rt /\ c_inv lt) \/
    (c_inv lt /\ c_inv rt))
    
val balance: c:color -> lt:rbtree -> ky:nat -> rt:rbtree ->
             Pure rbtree
             (requires (pre_balance c lt rt))
	     (ensures (fun r -> (is_T r)  /\
	                        ((h_inv r) /\
                                 ((c = B /\ Some.v(black_height r) = Some.v(black_height lt) + 1) \/
                                  (c = R /\ Some.v(black_height r) = Some.v(black_height lt)))) /\              
                                (c_inv r  \/
			        (T.col r = R /\ c = R /\ not_c_inv r /\ lr_c_inv r)))
			)
let balance c lt ky rt =
  match (c, lt, ky, rt) with
      (* combining the patterns below does not verify *)
    | (B, (T R (T R a x b) y c), z, d) -> T R (T B a x b) y (T B c z d)
    | (B, (T R a x (T R b y c)), z, d) -> T R (T B a x b) y (T B c z d)
    | (B, a, x, (T R (T R b y c) z d)) -> T R (T B a x b) y (T B c z d)
    | (B, a, x, (T R b y (T R c z d))) -> T R (T B a x b) y (T B c z d)
    | _ -> T c lt ky rt

val ins: t:rbtree -> k:nat ->
         Pure rbtree
         (requires (c_inv t /\ h_inv t))
	 (ensures (fun r -> (is_T r) /\

                            (h_inv r /\ black_height r = black_height t)
          
                            /\

                            (c_inv r \/
		            (is_T t /\ T.col r = R /\ T.col t = R /\ not_c_inv r /\ lr_c_inv r))))

let rec ins t x =
  match t with
    | E -> T R E x E
    | T c a y b ->
      if x < y then
	let lt = ins a x in
	balance c lt y b
      else if x = y then
	t
      else
	let rt = ins b x in	
	balance c a y rt

val make_black: t:rbtree -> Pure rbtree (requires (c_inv t /\ is_T t /\ h_inv t))
                            (ensures (fun r -> c_inv r /\ (is_T r /\ T.col r = B) /\ h_inv r))
let make_black t = match t with
  | T _ a x b -> T B a x b
  | _ -> assert(false); t

val insert: t:rbtree -> nat -> Pure rbtree
                               (requires (balanced_rbtree t))
			       (ensures (fun r -> balanced_rbtree r))
let insert t x = 
  let r = ins t x in  
  let r' = make_black r in
  r'
