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

val black_root: t:rbtree -> Tot bool
let black_root t = color_of t = B

val left_black_height: t:rbtree -> nat -> Tot nat
let rec left_black_height t n = match t with
  | E -> n
  | T B a _ _ -> left_black_height a (n + 1)
  | T R a _ _ -> left_black_height a n

val right_black_height: t:rbtree -> nat -> Tot nat
let rec right_black_height t n = match t with
  | E -> n
  | T B _ _ b -> right_black_height b (n + 1)
  | T R _ _ b -> right_black_height b n

val h_inv: t:rbtree -> Tot bool
let h_inv t = (left_black_height t 0) = (right_black_height t 0)

val c_inv: t:rbtree -> Tot bool
let rec c_inv t = match t with
  | E -> true
  | T R a _ b -> color_of a = B && color_of b = B && c_inv a && c_inv b
  | T B a _ b -> c_inv a && c_inv b

type balanced_rbtree (t:rbtree) = (is_E t \/ (is_T t && T.col t = B)) /\ h_inv t /\ c_inv t


val make_black: t:rbtree -> Pure rbtree (requires (c_inv t /\ is_T t))
                            (ensures (fun r -> c_inv r /\ (is_T r && T.col r = B)))
let make_black t = match t with
  | T _ a x b -> T B a x b
  | _ -> assert(false); E

type not_c_inv (t:rbtree) =
   (T.col t = R /\ T.col (T.left t) = R) \/
   (T.col t = R /\ T.col (T.right t) = R)

type lr_c_inv (t:rbtree) = c_inv (T.left t) /\ c_inv (T.right t)

type pre_balance (c:color) (lt:rbtree) (rt:rbtree) =
    (c = B /\ not_c_inv lt /\ lr_c_inv lt /\ c_inv rt) \/
    (c = B /\ not_c_inv rt /\ lr_c_inv rt /\ c_inv lt) \/
    (c_inv lt /\ c_inv rt)
    
val balance: c:color -> lt:rbtree -> ky:nat -> rt:rbtree ->
             Pure rbtree
                        (requires (pre_balance c lt rt))
			(ensures (fun r -> (is_T r) /\ (c_inv r \/
			                   (T.col r = R /\ c = R /\ not_c_inv r /\ lr_c_inv r)))
			)
let balance c lt ky rt =
  match (c, lt, ky, rt) with
    | (B, (T R (T R a x b) y c), z, d)
    | (B, (T R a x (T R b y c)), z, d)
    | (B, a, x, (T R (T R b y c) z d))
    | (B, a, x, (T R b y (T R c z d))) -> T R (T B a x b) y (T B c z d)	
    | _ -> T c lt ky rt

val ins: t:rbtree -> k:nat -> Pure rbtree
                              (requires (c_inv t))
			      (ensures (fun r -> (is_T r) /\ (c_inv r \/			      
			                         (is_T t /\ T.col r = R /\ T.col t = R /\ not_c_inv r /\ lr_c_inv r)))) (* why is is_T necessary in the second clause of disjunction ? T.col r = R should mean is_T t itself ? *)

let rec ins t x = match t with
  | E -> T R E x E    
  | T c a y b ->
    if x < y then
      (* without this let binding, fails to verify ? *)
      let lt = ins a x in
      balance c lt y b
    else if x = y then
      t
    else
      let rt = ins b x in
      balance c a y rt

val insert: t:rbtree -> nat -> Pure rbtree
                               (requires (balanced_rbtree t))
			       (ensures (fun x -> True))
let insert t x = 
  let r = ins t x in  
  let r' = make_black r in
  assert(is_T r' /\ T.col r' = B /\ c_inv r');
  r'
