module ProofRelevantRelation

module Mon = FStar.Algebra.Monoid
module L = FStar.List.Pure

let (<|) f x = f x
let ( |> ) x f = f x

let rel (a:Type0) = a -> a -> Type0

let rel_morphism (#a #b:Type0) (f:a -> b) (ra:rel a) (rb:rel b) =
  #x:a -> #y:a -> ra x y -> rb (f x) (f y)

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
  (wa:list (x:a & y:a & ra x y){
    match wa with
    | [] -> ya == za
    | _ -> free_transitive_rel_pred ra wa ya za
  })
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
