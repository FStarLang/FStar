module LowStar.Util
module HS = FStar.HyperStack
module B = LowStar.Buffer

private
let __reduce__ = ()
unfold let normal (#a:Type) (x:a) : a =
  FStar.Pervasives.norm
    [iota;
     zeta;
     delta_attr [`%__reduce__];
     primops;
     simplify]
     x

let buf_t = a:Type & B.buffer a

[@__reduce__]
let buf (#a:Type) (b:B.buffer a) : buf_t = (|a, b|)

/// Several internal forms that are also supposed to be normalized away during typechecking
/// DO NOT USE THESE DIRECTLY: use their counterparts marked "unfold" below
[@__reduce__]
private
let rec all_loc' (f:B.loc -> Type0) (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> f hd /\ all_loc' f tl

unfold
let all_loc f l = normal (all_loc' f l)

[@__reduce__]
private
let rec pairwise' (f:B.loc -> B.loc -> Type0) (l:list B.loc) =
  match l with
  | [] -> True
  | hd::tl -> all_loc (f hd) tl /\ pairwise' f tl

unfold
let pairwise f l = normal (pairwise' f l)

[@__reduce__]
private
let rec all_buf' (f:buf_t -> Type0) (l:list buf_t) =
  match l with
  | [] -> True
  | hd::tl -> f hd /\ all_buf' f tl

unfold
let all_buf f l = normal (all_buf' f l)

unfold
let all_live (h:HS.mem) (l:list buf_t) :GTot Type0 =
  normal (all_buf (fun (| _, b |) -> B.live h b) l)

unfold
let all_disjoint (l:list B.loc) = normal (pairwise B.loc_disjoint l)

[@__reduce__]
let rec foldr_loc (#a:Type) (l:list B.loc) (f:B.loc -> a -> GTot a) (x:a) : GTot a =
  match l with
  | [] -> x
  | hd::tl -> f hd (foldr_loc tl f x)

unfold
let loc_union_l (l:list B.loc) = normal (foldr_loc l B.loc_union B.loc_none)
