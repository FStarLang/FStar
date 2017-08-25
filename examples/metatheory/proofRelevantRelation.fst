module ProofRelevantRelation

module Mon = FStar.Algebra.Monoid
module L = FStar.List.Pure

let (<|) f x = f x
let ( |> ) x f = f x

(*! Basic definitions !*)

(* A proof relevant relation on a type `a` associates *)
(* to each pair `x y:a` a type of "proofs" *)
let rel (a:Type0) = a -> a -> Type0

(* A morphism between 2 relations `ra` on `a` and `rb` on `b` *)
(* over a function `f : a -> b` is a function mapping proofs of *)
(* relationship `x \`ra\` y` to proof of relationship `f x \`rb\` f y` *)
let rel_morphism (#a #b:Type0) (f:a -> b) (ra:rel a) (rb:rel b) =
  #x:a -> #y:a -> ra x y -> rb (f x) (f y)

(*! Various interesting structure that can equip a given relation !*)

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


(*! The free reflexive structure on a relation !*)

unopteq
type free_reflexive_rel (#a:Type0) (r:a -> a -> Type0) : rel a =
  | FRReturn : #x:a -> #y:a -> r x y -> free_reflexive_rel r x y
  | FRRefl : x:a -> free_reflexive_rel r x x

let frrefl_is_reflexive #a #r (x y:a) (w:free_reflexive_rel r x y) : Lemma (FRRefl? w ==> x == y) = ()

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


(*! The free symmetric structure on a relation !*)

let bswap (#a:Type) (b:bool) (f: a -> a -> Type0) (x y:a) = if b then f y x else f x y
type free_symmetric_rel (#a:Type0) (r:rel a) (x y : a) : Type0 =
   swap:bool &
   (* (if swap then r y x else r x y) *)
   (bswap #a swap r x y)

let coerce (#a b:Type) (x:a) : Pure b (requires (a == b)) (ensures (fun r -> a == b /\ r == x))
= x

let bswap_lemma (#a:Type) (f: a -> a -> Type0) : Lemma (forall b x y. bswap b f x y == bswap (not b) f y x) = ()

let bswap_not (#a:Type) (#b:bool) (#f:a -> a -> Type0) (#x #y:a) (w:bswap b f x y) : bswap (not b) f y x
= coerce (bswap (not b) f y x) w

let free_symmetric_rel_symmetric (#a:Type0) (r:rel a)
  : symmetric_structure (free_symmetric_rel r)
= fun #x #y w0 -> match w0 with | (| b, w |) ->
  (| not b, bswap_not w |)

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


(*! The free transitive structure on a relation !*)

let concat_valid (#a:Type0) (r:rel a) (w:(x:a & y:a & r x y)) ((y',z,p):a*a*Type0) : a*a*Type0 =
  let (|x, y, _|) = w in
  x, z, (y == y' /\ p)

let free_transitive_rel_pred (#a:Type0) (r:rel a) (l:list (x:a & y:a & r x y)) (x y:a) : Type0 =
  Cons? l /\
  (let (|x', _, _|) :: _ = l in x == x') /\
  Mktuple3?._3 (L.fold_right (concat_valid r) l (y,y,True))

type free_transitive_rel (#a:Type0) (r:rel a) (x y: a) : Type0 =
  l:list (x:a & y:a & r x y){free_transitive_rel_pred r l x y}

type almost_transitive (#a:Type0) (r:rel a) (x y:a) : Type0 =
  l:list (x:a & y:a & r x y){
    match l with
    | [] -> x == y
    | _ -> free_transitive_rel_pred r l x y
  }


let rec append_valid (#a:Type) (r:rel a) (#x #y #z:a) (wxy:free_transitive_rel r x y) (wyz:free_transitive_rel r y z)
  : Lemma (ensures Mktuple3?._3 (L.fold_right (concat_valid r) (wxy @ wyz) (z,z,True))) (decreases wxy)
=
  match wxy with
  | (| x', y', _ |)::[] ->
    assert (Mktuple3?._3 (L.fold_right (concat_valid r) wxy (y,y,True))) ;
    assert (x == x') ;
    assert (y == y') ;
    let [w] = wxy in
    assert (Mktuple3?._3 (concat_valid r w (L.fold_right (concat_valid r) wyz (z,z,True))))
  | (| x', u, _ |)::wuy ->
    assert (Mktuple3?._3 (L.fold_right (concat_valid r) wuy (y,y,True))) ;
    let wuy : free_transitive_rel r u y = wuy in
    append_valid #a r #u #y #z wuy wyz

let free_transitive_rel_transitive (#a:Type) (r:rel a) : transitive_structure (free_transitive_rel r) =
  fun (#x #y #z:a) (wxy:free_transitive_rel r x y) (wyz:free_transitive_rel r y z) ->
    append_valid r wxy wyz ;
    wxy @ wyz

let cons_almost_transitive (#a:Type) (r:rel a) (x y z:a) (wxy:r x y) (wyz:almost_transitive r y z)
  : Tot (free_transitive_rel r x z)
= (|x, y, wxy|) :: wyz

let tail_almost_transitive (#a:Type) (r:rel a) (x y z:a) (wxz:free_transitive_rel r x z)
  : Pure (almost_transitive r y z) (requires (Mkdtuple3?._2 (Cons?.hd wxz) == y)) (ensures (fun wyz -> wyz << wxz))
=
  (* assert (Mktuple3?._3 (L.fold_right (concat_valid r) wxz (z,z,True))) ; *)
  match wxz with
    | (|_,y', _|) :: [] -> assert(y' == y /\ y' == z) ; []
    | (|_,y',_|) :: wyz ->
      assert (y == y') ;
      assert (Mktuple3?._3 (L.fold_right (concat_valid r) wyz (z,z,True))) ;
      wyz

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
  | (|ya', ua, w|):: _ ->
    let ub = f ua in
    let wb' : rb xb ub = transb #xb #yb #ub wb (ff w) in
    let wa' = tail_almost_transitive ra ya ua za wa in
    let x = concat f ra rb ff transb xb ub wb' ua za wa' in
    x

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
    let (| _, u, w |) :: _ = w0 in
    let w0' = tail_almost_transitive ra x u y w0 in
    concat f ra rb ff transb (f x) (f u) (ff w) u y w0'


(*! The free congruence structure on a relation  (wrt a monoid of ctx)!*)

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


(*! Distributive laws !*)
(* A distributivity law is a morphism permutating 2 structures on relation *)
(* We use sym for symmetry, refl for reflexivity, trans for transitivity and congr for congruence *)
(* The defined laws are : *)
(* - sym o refl -> refl o sym *)
(* - trans o refl -> refl o trans *)
(* - congr o refl -> refl o congr *)
(* - sym o congr -> congr o sym *)
(* - congr o sym -> sym o congr *)
(* - sym o trans -> trans o sym *)
(* - congr o trans -> trans o congr *)

let id (#a:Type) (x:a) : a = x
let rel_morphism_id (#a:Type) = rel_morphism #a #a (id #a)

(* FAIL : see #1007 *)

#set-options "--z3rlimit 80 --max_fuel 0 --max_ifuel 2 --initial_fuel 0 --initial_ifuel 2"
(* This fails when inlined... (related to #1007) *)
private
let symm_refl_to_refl_sym_aux #a #b #r #x #y (w' : bswap b (free_reflexive_rel #a r) x y)
  : (free_reflexive_rel (free_symmetric_rel r)) x y
=
  match w' with
  | FRRefl #a' #r' _ -> FRRefl #a #(free_symmetric_rel r) x
  | FRReturn #a' #r' #_ #_ w -> FRReturn #a #(free_symmetric_rel r) #x #y (|b , w |)
#reset-options

let symm_refl_to_refl_sym (#a:Type) (r:rel a)
  : rel_morphism_id #a
      (free_symmetric_rel #a (free_reflexive_rel #a r))
      (free_reflexive_rel (free_symmetric_rel r))
= fun (#x #y:a) (w:free_symmetric_rel #a (free_reflexive_rel #a r) x y) ->
  let (|b, w'|) = w in f#a #b #r #x #y w'


(* FAIL : see #1007 *)

private
let filter_out_refl_aux (a:Type) (r:rel a) (x u y: a) (wxu:free_reflexive_rel r x u) (wuy:almost_transitive r u y)
  : Tot (almost_transitive r x y)
= match wxu with
  | FRReturn #a' #r' wxu' -> cons_almost_transitive r x u y wxu' wuy
  | FRRefl #a' #r' _ -> assert (x == u) ; wuy

private
let rec filter_out_refl (a:Type) (r:rel a)
  (x y:a)
  (wxy:free_transitive_rel #a (free_reflexive_rel #a r) x y)
  : Tot (wxy:almost_transitive r x y) (decreases wxy)
= let (| x, u, wxu |) = Cons?.hd wxy in
  let wuy = tail_almost_transitive (free_reflexive_rel #a r) x u y wxy in
  let wuy' : almost_transitive r u y = match wuy with
    | [] -> []
    | _ -> filter_out_refl a r u y wuy
  in
  filter_out_refl_aux a r x u y wxu wuy'

let trans_refl_to_refl_trans (#a:Type) (r:rel a)
  : rel_morphism_id #a
    (free_transitive_rel (free_reflexive_rel r))
    (free_reflexive_rel (free_transitive_rel r))
= fun (#x #y: a) (w:free_transitive_rel (free_reflexive_rel r) x y) ->
  match filter_out_refl a r x y w with
  | [] -> FRRefl x
  | wxy -> FRReturn wxy


let congr_refl_to_refl_congr (#a:Type) (r:rel a) (ctx:ctx_structure a)
  : rel_morphism_id #a
    (free_congruence_rel (free_reflexive_rel r) ctx)
    (free_reflexive_rel (free_congruence_rel r ctx))
= fun (#x #y:a) (w:free_congruence_rel (free_reflexive_rel r) ctx x y) ->
  let FCAct #_ #_ #_ #x0 #y0 w0 c = w in
  match w0 with
  | FRRefl #_ #_ x -> FRRefl (plug_in ctx c x0) (* (FCAct #a #r #ctx #x0 #x0  (Mon.Monoid?.unit (Ctx?.m ctx))) *)
  | FRReturn #_ #_ w -> FRReturn #a #(free_congruence_rel r ctx) #(plug_in ctx c x0) #(plug_in ctx c y0) (FCAct #a #r #ctx #x0 #y0 w c)

let sym_congr_to_congr_sym (#a:Type) (r:rel a) (ctx:ctx_structure a)
  : rel_morphism_id #a
    (free_symmetric_rel #a (free_congruence_rel #a r ctx))
    (free_congruence_rel #a (free_symmetric_rel #a r) ctx)
= fun (#x #y:a) (w:free_symmetric_rel #a (free_congruence_rel #a r ctx) x y) ->
  let (|b, FCAct #a #r #ctx #x0 #y0 w c|) = w in
  (* Not that surprising but the following (correct) line fails to verify *)
  (* FCAct #a #(free_symmetric_rel r) #ctx #(if b then y0 else x0) #(if b then x0 else y0) (|b, w|) c *)
  if b then
    FCAct #a #(free_symmetric_rel r) #ctx #y0 #x0 (|b, w|) c
  else
    FCAct #a #(free_symmetric_rel r) #ctx #x0 #y0 (|b, w|) c

let congr_sym_to_sym_congr (#a:Type) (r:rel a) (ctx:ctx_structure a)
  : rel_morphism_id #a
    (free_congruence_rel #a (free_symmetric_rel #a r) ctx)
    (free_symmetric_rel #a (free_congruence_rel #a r ctx))
= fun (#x #y:a) (w:free_congruence_rel #a (free_symmetric_rel #a r) ctx x y) ->
  let FCAct #_ #_ #_ #x0 #y0 w0 c = w in
  let (| b, w |) = (w0 <: free_symmetric_rel r x0 y0) in
  if b then
    (|b, FCAct #a #r #ctx #y0 #x0 w c|)
  else
    (|b, FCAct #a #r #ctx #x0 #y0 w c|)

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

let free_symmetric_rel_unit (#a:Type) (r:rel a) : rel_morphism_id #a r (free_symmetric_rel r) =
  fun (#x #y:a) (w:r x y) -> (|false, w|)

let free_transitive_rel_unit (#a:Type) (r:rel a) : rel_morphism_id #a r (free_transitive_rel r) =
  fun (#x #y:a) (w:r x y) -> [(|x, y, w|)]

let compose f g = fun x -> g (f x)

let rel_compose (#a #b #c:Type) (#f:a -> b) (#g:b -> c) (#ra:rel a) (#rb:rel b) (#rc:rel c)
  (ff:rel_morphism #a #b f ra rb)
  (gg:rel_morphism #b #c g rb rc)
  : rel_morphism #a #c (f `compose` g) ra rc
= fun #x #y w -> gg #(f x) #(f y) (ff #x #y w)

open FStar.FunctionalExtensionality

let free_transitive_rel_map (#a #b:Type) (f:a -> b) (ra:rel a) (rb:rel b) (ff:rel_morphism f ra rb)
  : rel_morphism f (free_transitive_rel ra) (free_transitive_rel rb) =
  let ra' = free_transitive_rel ra in
  let rb' = free_transitive_rel rb in
  let gg : rel_morphism f ra rb' =
    assert ((f `compose` id) `feq` f) ;
    ff `rel_compose` free_transitive_rel_unit rb
  in
  let trans = free_transitive_rel_transitive #b rb in
  let free : rel_morphism f ra' rb' = free_transitive_rel_free f ra rb' gg trans in
  free

(* Works *)
(* assume val a : Type0 *)
(* assume val r : a -> a -> Type0 *)
(* let r' = free_transitive_rel #a (free_symmetric_rel #a r) *)
(* let ff : rel_morphism #a #a id r r' = fun (#u #v:a) (w: r u v) -> *)
(*   (\* ([(|u, v, (| false, w |) |)] <: r' u v) *\) *)
(*   free_transitive_rel_unit (free_symmetric_rel r) (free_symmetric_rel_unit r w) *)

(* Works *)
(* let nontoplevel (a:Type) (r:rel a) = *)
(*   let r' = free_transitive_rel #a (free_symmetric_rel #a r) in *)
(*   let ff : rel_morphism #a #a id r r' = fun (#u #v:a) (w: r u v) -> *)
(*     free_transitive_rel_unit (free_symmetric_rel r) (free_symmetric_rel_unit r w) in *)
(*   () *)

(* let apply_rel_morph (#a:Type) (#r1 #r2:rel a) (f:rel_morphism_id #a r1 r2) (#x #y:a) (w:r1 x y) : r2 x y = f w *)

private
let swap_witness (#a:Type) (r:rel a) (#x #y:a) (w:r x y) : free_symmetric_rel r y x =
  (| true, w |)

private
let rec insert_sym_aux
  (#a:Type)
  (r:rel a)
  (x y z:a)
  (wyx:free_transitive_rel (free_symmetric_rel r) y x)
  (wyz:free_transitive_rel #a r y z)
  : Tot (free_transitive_rel (free_symmetric_rel #a r) z x) (decreases wyz)
=
  let r' = free_symmetric_rel r in
  let trans = free_transitive_rel_transitive #a r' in
  let (|y, u, wyu|) = Cons?.hd wyz in
  let wuy = free_transitive_rel_unit #a r' #u #y (swap_witness #a r #y #u wyu) in
  let wux = trans #u #y #x wuy wyx in
  match tail_almost_transitive r y u z wyz with
  | [] -> wux
  | wuz -> insert_sym_aux #a r x u z wux wuz

private
let insert_sym
  (#a:Type)
  (r:rel a)
  (x y:a)
  (wxy:free_transitive_rel #a r x y)
  : Tot (free_transitive_rel (free_symmetric_rel #a r) y x)
=
  let (|x, u, wxu|) = Cons?.hd wxy in
  let r' = free_symmetric_rel r in
  let wux = free_transitive_rel_unit #a r' #u #x (swap_witness #a r #x #u wxu) in
  match tail_almost_transitive r x u y wxy with
  | [] -> wux
  | wuy -> insert_sym_aux #a r x u y wux wuy

let sym_trans_to_trans_sym (#a:Type) (r:rel a)
  : rel_morphism_id #a
    (free_symmetric_rel #a (free_transitive_rel #a r))
    (free_transitive_rel #a (free_symmetric_rel #a r))
= fun (#x #y:a) (w:free_symmetric_rel #a (free_transitive_rel #a r) x y) ->
  let (|b, w|) = w in
  if b then
    insert_sym #a r y x w
  else
    free_transitive_rel_map #a #a id r (free_symmetric_rel r) (free_symmetric_rel_unit r) w

(* FAIL : Stale unification variable error *)
(* let sym_trans_to_trans_sym (#a:Type) (r:rel a) *)
(*   : rel_morphism_id #a *)
(*     (free_symmetric_rel #a (free_transitive_rel #a r)) *)
(*     (free_transitive_rel #a (free_symmetric_rel #a r)) *)
(* = fun (#x #y:a) (w:free_symmetric_rel #a (free_transitive_rel #a r) x y) -> *)
(*   let (|b, w|) = w in *)
(*   if not b then *)
(*     let r' = free_transitive_rel #a (free_symmetric_rel #a r) in *)
(*       let ff : rel_morphism #a #a id r r' = fun (#u #v:a) (w: r u v) ->  [(|u, v, (| false, w |) |)] <: r' u v in *)
(*     admit () *)
(*     (\* free_transitive_rel_free #a #a id r (free_symmetric_rel r) ff *\) *)
(*     (\*   (free_transitive_rel_transitive #a (free_symmetric_rel r)) #x #y w *\) *)
(*   else admit () *)

let plug_ctx (#a:Type) (r:rel a) (ctx:ctx_structure a) (c:Ctx?.ctx ctx)
  : rel_morphism #a #a (plug_in ctx c) r (free_congruence_rel r ctx)
= fun (#x #y:a) (w:r x y) ->
  FCAct #a #r w c

let congr_trans_to_trans_congr (#a:Type) (r:rel a) (ctx:ctx_structure a)
  : rel_morphism_id #a
    (free_congruence_rel #a (free_transitive_rel #a r) ctx)
    (free_transitive_rel #a (free_congruence_rel #a r ctx))
= fun (#x #y:a) (w:free_congruence_rel #a (free_transitive_rel #a r) ctx x y) ->
  let FCAct w c = w in
  free_transitive_rel_map #a #a (plug_in ctx c) r (free_congruence_rel r ctx) (plug_ctx #a r ctx c) w

