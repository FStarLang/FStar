module Update

assume val s : Type0
assume val p : s -> Type0
assume val upd : s_0:s -> p s_0 -> s
assume val id : s_0:s -> p s_0
assume val comp : #s_0:s -> p_0:p s_0 -> p (s_0 `upd` p_0) -> p s_0

assume UpdId : forall (s_0:s). {:pattern (s_0 `upd` (id s_0))} s_0 `upd` (id s_0) == s_0
assume UpdComp : forall (s_0:s) (p_0:p s_0) (p_1:p (s_0 `upd` p_0)).
  {:pattern (s_0 `upd` (p_0 `comp` p_1)) \/ (s_0 `upd` p_0 `upd` p_1)}
  s_0 `upd` (p_0 `comp` p_1) == s_0 `upd` p_0 `upd` p_1

let eq_rec (#a b:Type) (x:a) : Pure b (requires (a == b)) (ensures (fun r -> r === x)) = x

assume LeftUnitality : forall (s_0:s) (p_0: p s_0). (id s_0) `comp` p_0 == p_0
assume RightUnitality : forall (s_0:s) (p_0: p s_0). p_0 `comp` (id (s_0 `upd` p_0)) == p_0
assume Associativity : forall (s_0:s) (p_0:p s_0) (p_1:p (s_0 `upd` p_0)) (p_2:p (s_0 `upd` p_0 `upd` p_1)).
  p_0 `comp` (p_1 `comp` p_2) == p_0 `comp` p_1 `comp` (eq_rec (p (s_0 `upd` (p_0 `comp` p_1))) p_2)

type upd_t (a:Type) = s_0:s -> M (p s_0 * a)
let return (a:Type) (x:a) : upd_t a = fun s_0 -> id s_0, x
let bind (a b:Type) (m:upd_t a) (f:a -> upd_t b) : upd_t b =
  fun s_0 ->
    let p_0, x = m s_0 in
    let p_1, y = f x (s_0 `upd` p_0) in
    p_0 `comp` p_1, y

type upd_star (a:Type) = s_0:s -> ((p s_0 * a) -> Type0) -> Type0
let return_star (a:Type) (x:a) : upd_star a = fun s_0 pred -> pred (id s_0, x)
let bind_star (a b:Type) (m:upd_star a) (f:a -> upd_star b) : upd_star b =
  fun s_0 pred ->
    m s_0 (fun (p_0, x) ->
      f x (s_0 `upd` p_0) (fun (p_1, y) ->
        pred (p_0 `comp` p_1, y)
      ))

type upd_elab (a:Type) (wp: upd_star a) = s_0:s -> PURE (p s_0 * a) (wp s_0)
let return_elab (a:Type) (x:a) : upd_elab a (return_star a x) = fun s_0 -> (id s_0, x)
(* As usual we need to internalize monotonicity to be able to prove the bind... *)
#set-options "--admit_smt_queries true"
let bind_elab (a b:Type) (wpm:upd_star a) (m:upd_elab a wpm) (wpf:a -> upd_star b) (f:x:a -> upd_elab b (wpf x)) : upd_elab b (bind_star a b wpm wpf)=
  fun s_0 ->
    let p_0, x = m s_0 in
    let p_1, y = f x (s_0 `upd` p_0) in
    p_0 `comp` p_1, y
#set-options "--admit_smt_queries false"
