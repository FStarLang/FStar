module ProofRelevantRelation

module Mon = FStar.Algebra.Monoid
module L = FStar.List.Pure

let (<|) f x = f x
let ( |> ) x f = f x

let rel (a:Type0) = a -> a -> Type0

let rel_morphism (#a #b:Type0) (f:a -> b) (ra:rel a) (rb:rel b) =
  #x:a -> #y:a -> ra x y -> rb (f x) (f y)

(* let rel_obj = a:Type & rel a *)

(* noeq *)
(* type rel_morphism' (x y:rel_obj) = *)
(*   | RelMorphism : *)
(*     obj:((dfst x) -> (dfst y)) -> *)
(*     arr:rel_morphism #(dfst x) #(dfst y) obj (dsnd x) (dsnd y) -> *)
(*     rel_morphism' x y *)

(* noeq *)
(* type monad_rel (t : (a:Type & rel a -> a:Type & rel a)) = *)
(*   | MonadRel : *)
(*     unit:(#x:(a:Type & rel a) -> rel_morphism' x (t x)) -> *)
(*     mult:(#x:(a:Type & rel a) -> rel_morphism' (t (t x)) (t x)) -> *)
(*     monad_rel t *)

let reflexive_structure (#a:Type) (r:rel a) = x:a -> r x x

let symmetric_structure (#a:Type) (r:rel a) = #x:a -> #y:a -> r x y -> r y x

let transitive_structure (#a:Type) (r:rel a) = #x:a -> #y:a -> #z:a -> r x y -> r y z -> r x z

unopteq
type ctx_structure (a:Type) =
  | Ctx :
    ctx:Type ->
    m:Mon.monoid ctx ->
    l:Mon.left_action m a ->
    ctx_structure a

let plug_in (#a:Type) (ctx:ctx_structure a) (x:Ctx?.ctx ctx) (y:a) : a =
  Mon.LAct?.act (Ctx?.l ctx) x y

let congruence_structure (#a:Type) (r:rel a) (ctx:ctx_structure a) =
  #x:a -> #y:a -> w:r x y -> c:(Ctx?.ctx ctx) -> r (plug_in ctx c x) (plug_in ctx c y)

unopteq
type free_reflexive_rel (#a:Type0) (r:a -> a -> Type0) : rel a =
  | FRReturn : #x:a -> #y:a -> r x y -> free_reflexive_rel r x y
  | FRRefl : x:a -> free_reflexive_rel r x x


let free_reflexive_rel_reflexive (#a:Type) (r:rel a)
  : reflexive_structure (free_reflexive_rel r)
= FRRefl

let free_reflexive_rel_free
  (#a #b:Type0)
  (f: a -> b)
  (ra:rel a)
  (rb:rel b)
  (ff:rel_morphism f ra rb)
  (reflb:reflexive_structure rb)
  : rel_morphism f (free_reflexive_rel ra) rb
=
  fun (#x #y:a) (w0:free_reflexive_rel ra x y) ->
    match w0 with
    | FRReturn w -> ff #x #y w
    | FRRefl x -> reflb (f x)


type free_symmetric_rel (#a:Type0) (r:rel a) (x y : a) : Type0 = swap:bool & (if swap then r y x else r x y)

let free_symmetric_rel_symmetric (#a:Type0) (r:rel a)
  : symmetric_structure (free_symmetric_rel r)
= fun #x #y w0 -> match w0 with | (| b, w |) -> (| not b, w |)

let free_symmetric_rel_free
  (#a #b:Type0)
  (f: a -> b)
  (ra:rel a)
  (rb:rel b)
  (ff:rel_morphism f ra rb)
  (symb:symmetric_structure rb)
  : rel_morphism f (free_symmetric_rel ra) rb
=
  fun (#x #y:a) (w0:free_symmetric_rel ra x y) ->
    match w0 with
    | (| b , w |) -> if b then symb #(f y) #(f x) <| ff w else ff w

let concat_valid (#a:Type0) (r:rel a) ((|x, y, _|): (x:a & y:a & r x y)) ((z,p):a*Type0) : a*Type0 =
  x, (y == z /\ p)

let free_transitive_rel_pred (#a:Type0) (r:rel a) (l:list (x:a & y:a & r x y)) (x y:a) : Type0 =
  Cons? l /\
  (let (|x', _, _|) :: _ = l in x == x') /\
  snd (L.fold_right (concat_valid r) l (y,True))

type free_transitive_rel (#a:Type0) (r:rel a) (x y: a) : Type0 =
  l:list (x:a & y:a & r x y){free_transitive_rel_pred r l x y}

type almost_transitive (#a:Type0) (r:rel a) (x y:a) : Type0 =
  l:list (x:a & y:a & r x y){
    match l with
    | [] -> x == y
    | _ -> free_transitive_rel_pred r l x y
  }


let rec append_valid (#a:Type) (r:rel a) (#x #y #z:a) (wxy:free_transitive_rel r x y) (wyz:free_transitive_rel r y z)
  : Lemma (ensures (snd (L.fold_right (concat_valid r) (wxy @ wyz) (z, True)))) (decreases wxy)
=
  match wxy with
  | (| x', y', _ |)::[] -> assert (x == x' /\ y == y')
  | (| x', u, _ |)::wuy -> assert (x == x') ; append_valid #a r #u #y #z wuy wyz

let free_transitive_rel_transitive (#a:Type) (r:rel a) : transitive_structure (free_transitive_rel r) =
  fun (#x #y #z:a) (wxy:free_transitive_rel r x y) (wyz:free_transitive_rel r y z) ->
    append_valid r wxy wyz ;
    wxy @ wyz

let rec concat
  (#a #b:Type0)
  (f: a -> b)
  (ra:rel a)
  (rb:rel b)
  (ff:rel_morphism f ra rb)
  (transb:transitive_structure rb)
  (xb yb:b)
  (wb:rb xb yb)
  (ya za:a)
  (wa:almost_transitive ra ya za)
  : Pure (rb xb (f za)) (requires (yb == f ya)) (ensures (fun _ -> True)) (decreases wa)
=
  match wa with
  | [] -> wb
  | (|ya', ua, w|)::wa' ->
    let ub = f ua in
    let wb' : rb xb ub = transb #xb #yb #ub wb (ff w) in
    concat f ra rb ff transb xb ub wb' ua za wa'

let free_transitive_rel_free
  (#a #b:Type0)
  (f: a -> b)
  (ra:rel a)
  (rb:rel b)
  (ff:rel_morphism f ra rb)
  (transb:transitive_structure rb)
  : rel_morphism f (free_transitive_rel ra) rb
=
  fun (#x #y:a) (w0:free_transitive_rel ra x y) ->
    let (| _, u, w |) :: w0' = w0 in
    concat f ra rb ff transb (f x) (f u) (ff w) u y w0'

unopteq
type free_congruence_rel (#a:Type0) (r:a -> a -> Type0) (ctx:ctx_structure u#0 u#0 a) : rel a =
  | FCAct : #x:a -> #y:a -> r x y -> c:Ctx?.ctx ctx -> free_congruence_rel r ctx (plug_in ctx c x) (plug_in ctx c y)

let free_congruence_rel_congruence (#a:Type0) (r:a -> a -> Type0) (ctx:ctx_structure a)
  : congruence_structure (free_congruence_rel r ctx) ctx
= fun (#x #y:a) (w0:free_congruence_rel r ctx x y) (c:Ctx?.ctx ctx) ->
  match w0 with
  | FCAct #_ #r' #_ #x' #y' w0 c0 ->
    assert (r' == r);
    let c' = Mon.Monoid?.mult (Ctx?.m ctx) c c0 in
    FStar.Classical.give_witness (Mon.LAct?.mult_lemma (Ctx?.l ctx)) ;
    assert (plug_in ctx c x == plug_in ctx c' x') ;
    assert (plug_in ctx c y == plug_in ctx c' y') ;
    FCAct #_ #_ #_ #x' #y' w0 c'

unopteq
type ctx_morphism (#a #b:Type) (f:a -> b) (ctxa:ctx_structure a) (ctxb:ctx_structure b) =
  | CtxMorphism :
    mf:(Ctx?.ctx ctxa -> Ctx?.ctx ctxb) ->
    mmf:(Mon.monoid_morphism mf (Ctx?.m ctxa) (Ctx?.m ctxb)) ->
    lf:(Mon.left_action_morphism f mf (Ctx?.l ctxa) (Ctx?.l ctxb)) ->
    ctx_morphism f ctxa ctxb

let free_congruence_rel_free
  (#a #b:Type0)
  (f: a -> b)
  (ra:rel a)
  (rb:rel b)
  (ff:rel_morphism f ra rb)
  (ctxa:ctx_structure a)
  (ctxb:ctx_structure b)
  (fctx:ctx_morphism f ctxa ctxb)
  (congb:congruence_structure rb ctxb)
  : rel_morphism f (free_congruence_rel ra ctxa) rb
=
  fun (#x #y:a) (w0:free_congruence_rel ra ctxa x y) ->
    match w0 with
    | FCAct #_ #_ #_ #x' #y' w c ->
      let xb = f x' in
      let yb = f y' in
      let cb = CtxMorphism?.mf fctx c in
      FStar.Classical.give_witness (CtxMorphism?.lf fctx) ;
      assert (plug_in ctxb cb xb == f (plug_in ctxa c x')) ;
      assert (plug_in ctxb cb yb == f (plug_in ctxa c y')) ;
      congb #xb #yb (ff #x' #y' w) cb


(* Distributive laws *)
let id (#a:Type) (x:a) : a = x
let rel_morphism_id (#a:Type) = rel_morphism #a #a (id #a)

(* FAIL : see #1007 *)

(* let symm_refl_to_refl_sym (#a:Type) (r:rel a) *)
(*   : rel_morphism_id #a *)
(*       (free_symmetric_rel #a (free_reflexive_rel #a r)) *)
(*       (free_reflexive_rel (free_symmetric_rel r)) *)
(* = fun (#x #y:a) (w:free_symmetric_rel #a (free_reflexive_rel #a r) x y) -> *)
(*   match w with *)
(*   | (| b, FRRefl x |) -> FRRefl x *)
(*   | (| b, FRReturn w |) -> FRReturn (|b, w|) *)


(* FAIL : see #1007 *)

(* private *)
(* let rec filter_out_refl (a:Type) (r:rel a) *)
(*   (x y:a) *)
(*   (wxy:free_transitive_rel #a (free_reflexive_rel #a r) x y) *)
(*   : Tot (wxy:almost_transitive r x y) (decreases wxy) *)
(* = match wxy with *)
(*   | [FRRefl _] -> [] *)
(*   | FRRefl _ :: wxy' -> filter_out_refl a x y wxy' *)
(*   | FRReturn #x #u wxu :: wuy -> wxu :: (filter_out_refl a x y wuy) *)

(* let trans_refl_to_refl_trans (#a:Type) (r:rel a) *)
(*   : rel_morphism #a #a *)
(*     (free_transitive_rel a (free_reflexive_rel a r)) *)
(*     (free_reflexive_rel a (free_transitive_rel a r)) *)
(* = fun (#x #y: a) (w:free_transitive_rel a (free_reflexive_rel a r) x y) -> *)
(*   match filter_out_refl x y w with *)
(*   | [] -> FRRefl x *)
(*   | wxy -> FRReturn wxy *)

(* let congr_refl_to_refl_congr (#a:Type) (r:rel a) (ctx:ctx_structure a) *)
(*   : rel_morphism #a #a *)
(*     (free_congruence_rel a (free_symmetric_rel a r) ctx) *)
(*     (free_symmetric_rel (free_congruence_rel a r ctx)) *)
(* = fun (#x #y:a) (w:free_congruence_rel a (free_symmetric_rel a r) ctx x y) -> *)
(*   match w with *)
(*   | FCAct (FRRefl x) c -> FRRefl (FCAct (plug_in c x) (Mon.Monoid?.unit (Ctx?.m ctx))) *)
(*   | FCAct (FRReturn w) c -> FRReturn (FCAct w c) *)

(* let sym_congr_to_congr_sym (#a:Type) (r:rel a) (ctx:ctx_structure a) *)
(*   : rel_morphism_id #a *)
(*     (free_symmetric_rel #a (free_congruence_rel #a r ctx)) *)
(*     (free_congruence_rel #a (free_symmetric_rel #a r) ctx) *)
(* = fun (#x #y:a) (w:free_symmetric_rel #a (free_congruence_rel #a r ctx) x y) -> *)
(*   let (|b, FCAct w c|) = w in FCAct (|b, w|) c *)

(* let congr_sym_to_sym_congr (#a:Type) (r:rel a) (ctx:ctx_structure a) *)
(*   : rel_morphism #a #a *)
(*     (free_congruence_rel a (free_symmetric_rel a r) ctx) *)
(*     (free_symmetric_rel a (free_congruence_rel a r ctx)) *)
(* = fun (#x #y:a) (w:free_congruence_rel a (free_symmetric_rel a r) ctx x y) -> *)
(*   let FCAct (|b, w|) c = w in (|b, FCAct w c|) *)

(* private *)
(* let rec insert_sym *)
(*   (#a:Type) *)
(*   (r:rel a) *)
(*   (b:bool) *)
(*   (x y z:a) *)
(*   (wacc:(if b then almost_transitive (free_symmetric_rel #a r) y x else list unit)) *)
(*   (w:free_symmetric_rel #a r y z) *)
(*   : Tot (free_transitive_rel (free_transitive_rel #a r) (if b then z else y) (if b then x else z)) (decreases w) *)
(* = match w with *)
(*   | [(| y, z, w0|)] -> *)
(*     if b then *)
(*       (|z, y, (|b, w0|)|) :: wacc *)
(*     else *)
(*       [(|y, z, (|b, w0|)|)] *)
(*   | (|y, u, w0|)::w -> *)
(*     if b then *)
(*       insert_sym r b x u z ((|u, y, (|b, w0|)|)::wacc) w *)
(*     else *)
(*       (|y, u, (|b, w0|)|) :: insert_sym r b x u z wacc w *)

(* let sym_trans_to_trans_sym (#a:Type) (r:rel a) *)
(*   : rel_morphism #a #a *)
(*     (free_symmetric_rel a (free_transitive_rel a r)) *)
(*     (free_transitive_rel a (free_symmetric_rel a r)) *)
(* = fun (#x #y:a) (w:free_symmetric_rel a (free_transitive_rel a r)) -> *)
(*   let (|b, w|) = w in *)
(*   insert_sym r b x x y [] w *)

(* let congr_trans_to_trans_congr (#a:Type) (r:rel a) *)
(*   : rel_morphism #a #a *)
(*     (free_congruence_rel a (free_transitive_rel a r)) *)
(*     (free_transitive_rel a (free_congruence_rel a r)) *)
(* =  *)
