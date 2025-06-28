module Bug3120a

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical
open FStar.Monotonic.Pure

(** Precondition decoding **)

type decode_pre (code : Type u#a) =
  code -> Type0

(* Basically unit *)
type ret_code : Type u#a =
| Triv

let ret_decode : decode_pre ret_code =
  function
  | Triv -> True

noeq
type bind_code (#a : Type u#a) (ac : Type u#a) (bc : a -> Type u#b) : Type u#(max a b) =
| BL : ac -> bind_code #a ac bc
| BR : x:a -> bc x -> bind_code #a ac bc

let bind_decode #a #ac ad (#bc : a -> Type0) (bd : (x:a -> decode_pre (bc x))) :
  decode_pre (bind_code #a ac bc)
= function
  | BL c -> ad c
  | BR x c -> bd x c

let req_code = ret_code

let req_decode (pre : Type0) : decode_pre req_code =
  function
  | Triv -> pre

(** Computation monad **)

noeq
type m (#code : Type u#a) (#dc : decode_pre code) (a : Type u#a) : Type u#a =
| Ret : a -> m #code #dc a
| Req : c:code -> (squash (dc c) -> m #code #dc a) -> m #code #dc a
(* | Read : (int -> m #code #dc a) -> m #code #dc a
| Write : int -> m #code #dc a -> m #code #dc a *)

let m_ret #a (x : a) : m #ret_code #ret_decode a =
  Ret x

(* Not very elegant to traverse the whole term for a noop *)
let rec m_lift #a #b #ac #ad (#bc : a -> _) (#bd : a -> _) (#x : a) (fx : m #(bc x) #(bd x) b) :
  m #(bind_code ac bc) #(bind_decode #a #ac ad #bc bd) b =
  match fx with
  | Ret y -> Ret y
  | Req c k -> Req (BR x c) (fun z -> m_lift (k ()))

let rec m_bind #a #b #ac #ad (#bc : a -> _) (#bd : a -> _) (u : m #ac #ad a) (f : (x:a -> m #(bc x) #(bd x) b)) : m #(bind_code ac bc) #(bind_decode #a #ac ad #bc bd) b =
  match u with
  | Ret x -> m_lift (f x)
  | Req c k -> Req (BL c) (fun z -> m_bind (k ()) f)

let m_req (p : Type0) : m #req_code #(req_decode p) (squash p) =
  Req Triv (fun h -> Ret h)

(** Specification monad **)

type event =
| ERead : int -> event
| EWrite : int -> event

type trace = list event

let hist_append (tr : trace) (hist : trace) : trace =
  tr @ rev hist

let wpre = trace -> Type0
let wpost a = trace -> a -> Type0

let wp a = wpost a -> wpre

unfold
let _wle #a (w1 w2 : wp a) =
  forall post hist. w2 post hist ==> w1 post hist

let wle #a (w1 w2 : wp a) =
  _wle w1 w2

unfold
let _w_return #a (x : a) : wp a =
  fun post hist -> post [] x

let w_return (#a:Type u#a) (x : a) : wp a =
  _w_return x

unfold
let _w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post hist -> w (fun tr x -> wf x post (hist_append tr hist)) hist

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  _w_bind w wf

let w_req (p : Type0) : wp (squash p) =
  fun post hist -> p /\ post [] (Squash.get_proof p)

(** Effect observation **)

let rec theta #ac #ad #a (u : m #ac #ad a) : wp a =
  match u with
  | Ret x -> w_return x
  | Req c k -> w_bind (w_req (ad c)) (fun x -> theta (k ()))

(** Dijkstra monad **)

let dm #ac #ad a (w : wp a) =
  c : m #ac #ad a { theta c `wle` w }

let d_ret #a (x : a) : dm a (w_return x) =
  m_ret x

let theta_bind #ac #ad #a #b #bc (#bd : a -> _)
  (u : m #ac #ad a) (f : (x : a) -> m #(bc x) #(bd x) b) :
  Lemma (theta (m_bind u f) `wle` w_bind (theta u) (fun x -> theta (f x)))
= admit ()

let d_bind #ac #ad #a #bc (#bd : a -> _) #b #w (#wf : a -> wp b)
  (u : dm #ac #ad a w) (f : (x : a) -> dm #(bc x) #(bd x) b (wf x)) :
  dm b (w_bind w wf) =
  theta_bind u f ;
  assume (theta (m_bind u f) `wle` w_bind w wf) ;
  m_bind u f

let d_req (p : Type0) : dm (squash p) (w_req p) =
  m_req p

let d_subcomp #ac #ad #a #w1 #w2 (u : dm #ac #ad a w1) :
  Pure (dm a w2) (requires w1 `wle` w2) (ensures fun _ -> True)
= u

let w_if_then_else #a (w1 w2 : wp a) (b : bool) : wp a =
  fun post hist -> (b ==> w1 post hist) /\ (~ b ==> w2 post hist)

(* TODO: Maybe we need an if on codes and decoding functions. *)
let if_then_else #ac #ad (a : Type) (w1 w2 : wp a) (f : dm #ac #ad a w1) (g : dm #ac #ad a w2) (b : bool) : Type =
  dm #ac #ad a (w_if_then_else w1 w2 b)

let elim_pure (#a:Type u#a) #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= elim_pure_wp_monotonicity_forall u#a () ;
  f ()

unfold
let wlift #a (w : pure_wp a) : wp a =
  fun post hist -> w (post [])

let as_requires_wlift (#a:Type u#a) (w : pure_wp a) :
  Lemma (forall post hist. wlift w post hist ==> as_requires w)
= assert (forall post (x : a). post x ==> True) ;
  elim_pure_wp_monotonicity w ;
  assert (forall post. w post ==> w (fun _ -> True)) ;
  assert (forall post. (True ==> w post) ==> w (fun _ -> True))
let lift_pure (a : Type u#0) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : dm a (wlift w) =
  elim_pure_wp_monotonicity w ;
  as_requires_wlift w ;
  d_bind #_ #_ #_ #_ #_ #_ #_ #(fun _ -> w_return (elim_pure #a #w f)) (d_req (as_requires w)) (fun _ ->
    let r = elim_pure #a #w f in
    let r' : dm a (w_return r) = d_ret r in
    r'
  )

(** Recast return and bind so that they have effect-friendly types **)

let ret a (x : a) : dm a (_w_return x) =
  d_ret x

let bind a b #ac #ad #bc #bd w wf u f : dm b (_w_bind w wf) =
  d_bind #ac #ad #a #bc #bd #b #w #wf u f

let subcomp #ac #ad a w1 w2 (c : dm #ac #ad a w1) :
  Pure (dm a w2) (requires w1 `_wle` w2) (ensures fun _ -> True)
= d_subcomp c

let _dm a ac ad w =
  dm #ac #ad a w

(** Effect **)

(** Currently this fails because it wants only one universe, but I can't set
    the two universes to be the same.
**)

(* Fails since `bind` is not universe-polymorphic enough, but should not crash *)
[@@expect_failure [115]]
total
reifiable
reflectable
effect {
  IOw (a : Type u#a) (ac : Type u#a) (ad : decode_pre ac) (w : wp a)
  with {
    repr         = _dm ;
    return       = ret ;
    bind         = bind ;
    subcomp      = subcomp ;
    if_then_else = if_then_else
  }
}
