module RunST

(* This file used to demonstrate a layered effect indexed by read/write/raise
   labels.  Layered effects and their indices are gone in this fork, so the
   example is now just the underlying free state-and-exception monad, written
   with let! notation. *)

open FStar.Tactics.V2

type eff_label =
  | RD
  | WR
  | EXN

let coerce #a #b (x:a{a == b}) : b = x

assume val unreachable : #a:Type0 -> unit -> Pure a (requires False) (ensures (fun _ -> False))

noeq
type action : inp:Type0 -> out:Type0 -> st0:Type0 -> st1:Type0 -> Type =
  | Read  : #st:Type0 -> action unit st st st
  | Write : #st0:Type0 -> #st1:Type0 -> action st1 unit st0 st1
  | Raise : #st0:Type0 -> #st1:Type0 -> action exn Prims.empty st0 st1

noeq
type repr (a:Type0) : st0:Type0 -> st1:Type0 -> Type =
  | Return : #s:Type0 -> x:a -> repr a s s
  | Op    : #i:Type0 -> #o:Type0 -> #st0:Type0 -> #st1:Type0 -> #st2:Type0 ->
            act:action i o st0 st1 -> i -> k:(o -> repr a st1 st2) -> repr a st0 st2

let return (#a:Type0) (#s:Type0) (x:a) : repr a s s = Return x

let rec bind (#a #b:Type0) (#st0 #st1 #st2:Type0)
  (c:repr a st0 st1) (f:a -> repr b st1 st2) : Tot (repr b st0 st2)
  = match c with
    | Return x -> f x
    | Op act i k -> Op act i (fun o -> bind (k o) f)

let (let!) (#a #b:Type0) (#st0 #st1 #st2:Type0)
  (m:repr a st0 st1) (f:a -> repr b st1 st2) : repr b st0 st2 =
  bind m f

let get #s () : repr s s s = Op Read () Return

let put #si #so (x:so) : repr unit si so = Op Write x Return

let raise #a #si #so (e:exn) : repr a si so = Op Raise e Return

let test0 (x y:int) : repr int int int =
  let! z = get () in
  if x + z > 0 then return 0 else return 1

let test1 (x y:int) : repr int int int =
  let! z = get () in
  if x + z > 0 then return 0 else let! _ = put 42 in return (y - z)

let labpoly #s0 (f g:unit -> repr int s0 s0) : repr int s0 s0 =
  let! x = f () in
  let! y = g () in
  return (x + y)

let termination_hack (i:int) : y:int{y << i} = admit(); i - 1

let rec aux (i:int) : Tot (repr unit int int) (decreases i) =
  if i > 0
  then let! s = get () in
       let! _ = put (s + i) in
       aux (termination_hack i)
  else return ()

let sumn #st (n:nat) : repr int st int =
  let! _ = put 0 in
  let! _ = aux n in
  get ()

let sumst #st (n:nat) : repr int st st =
  let! old = get () in
  let! _ = put 0 in
  let! _ = aux n in
  let! res = get () in
  let! _ = put old in
  return res

let rec _runST (#a:Type0) #si #sf (c:repr a si sf) (s0:si) : Tot (option (a & sf)) (decreases c) =
  match c with
  | Return x -> Some (x, s0)
  | Op Read _ k -> _runST (k s0) s0
  | Op Write s k -> _runST (k ()) s
  | Op Raise _ _ -> None

let runST #a #si #sf (c:unit -> repr a si sf) (s0:si) : Tot (option (a & sf)) =
  _runST (c ()) s0

let test_run_st : option int =
  match runST (fun () -> sumn 5) () with
  | Some xs -> Some (fst xs)
  | _ -> None

let rec _catchST (#a:Type0) #si #sf (stt:Type0) (c:repr a si sf) (s0:si)
  : Tot (repr (a & sf) stt stt) (decreases c)
  = match c with
    | Return x -> Return (x, s0)
    | Op Read _ k -> _catchST stt (k s0) s0
    | Op Write s k -> _catchST stt (k ()) s
    | Op Raise e k -> raise e

let catchST #a #st #si #sf (c:unit -> repr a si sf) (s0:si) : repr (a & sf) st st =
  _catchST st (c ()) s0

let rec _catchE (#a:Type0) #si #sf (c:repr a si sf) (h:(#si':Type0 -> repr a si' sf))
  : Tot (repr a si sf) (decreases c)
  = match c with
    | Return x -> Return x
    | Op Raise _ _ -> h #si
    | Op act i k -> Op act i (fun o -> _catchE (k o) h)

let catchE #a #si #sf (c:unit -> repr a si sf) (h:(#si':Type0 -> unit -> repr a si' sf))
  : repr a si sf =
  _catchE (c ()) (fun #si' -> h #si' ())

exception EE

let coerce_st_to (t:Type0) : repr unit t t = return ()

let __c1 () : repr int unit bool =
  let! _ = put "hello" in
  let! _ = raise #unit #string #unit EE in
  let! _ = coerce_st_to unit in
  let! _ = put true in
  return 42

let __h1 #si () : repr int si bool =
  let! _ = put false in
  return 42

let test_catch0 () : repr int unit bool = catchE __c1 __h1

let test_catch #a () : repr int a a =
  let! old = get () in
  let! _ = put () in
  let! r = catchE __c1 __h1 in
  let! _ = put old in
  return r

let puresum #st (n:nat) : repr int st st =
  let! xs = catchST (fun () -> sumn 42) 0 in
  return (fst xs)

let rec interp_pure_tree #a #st0 #st1 (t:repr a st0 st1) : Tot a (decreases t) =
  match t with
  | Return x -> x
  | Op _ _ _ -> admit()

let interp_pure #a #st0 #st1 (f:unit -> repr a st0 st1) : Tot a = interp_pure_tree (f ())

inline_for_extraction
let xxx = interp_pure (fun () -> puresum #unit 10)

let rec interp_rd_tree #a #st (t:repr a st st) (s:st) : Tot a (decreases t) =
  match t with
  | Return x -> x
  | Op Read _ k -> interp_rd_tree (k s) s
  | _ -> admit()

let interp_rd #a #st (f:unit -> repr a st st) (s:st) : Tot a = interp_rd_tree (f ()) s

let rec interp_rdwr_tree #a #st0 #st1 (t:repr a st0 st1) (s:st0)
  : Tot (a & st1) (decreases t)
  = match t with
    | Return x -> (x, s)
    | Op Read _ k -> interp_rdwr_tree (k s) s
    | Op Write s k -> interp_rdwr_tree (k ()) s
    | _ -> admit()

let interp_rdwr #a #st0 #st1 (f:unit -> repr a st0 st1) (s:st0) : Tot (a & st1) =
  interp_rdwr_tree (f ()) s
