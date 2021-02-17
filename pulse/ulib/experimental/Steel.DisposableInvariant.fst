module Steel.DisposableInvariant
open Steel.Effect
open Steel.Memory
open Steel.FractionalPermission
module A = Steel.Effect.Atomic
#push-options "--ide_id_info_off"
open Steel.Reference
open FStar.Ghost
let ghostref (a:Type) = ref (erased a)

let ghost_pts_to (#a:Type) (r:ghostref a) ([@@@smt_fallback]p:perm) ([@@@smt_fallback]x:erased a) =
  pts_to #(erased a) r p (hide x)

assume
val alloc_ghost (#a:Type) (#u:_) (x:erased a)
  : SteelAtomicT (ghostref a) u unobservable
    emp
    (fun r -> ghost_pts_to r full_perm x)


assume
val split_ghost (#a:Type) (#u:_)
                (#[@@@framing_implicit] p:perm)
                (#[@@@framing_implicit] x:erased a)
                (r:ghostref a)
  : SteelAtomicT unit u unobservable
    (ghost_pts_to r p x)
    (fun _ -> ghost_pts_to r (half_perm p) x `star`
           ghost_pts_to r (half_perm p) x)

assume
val gather_ghost (#a:Type) (#u:_)
                 (#[@@@framing_implicit]p0:perm)
                 (#[@@@framing_implicit]p1:perm)
                 (#[@@@framing_implicit]x:erased a)
                 (r:ghostref a)
  : SteelAtomicT unit u unobservable
    (ghost_pts_to r p0 x `star`
     ghost_pts_to r p1 x)
    (fun _ -> ghost_pts_to r (sum_perm p0 p1) x)

assume
val write_ghost (#a:Type) (#u:_) (#x:erased a) (r:ghostref a) (v:erased a)
  : SteelAtomicT unit u unobservable
    (ghost_pts_to r full_perm x)
    (fun _ -> ghost_pts_to r full_perm v)


[@@__reduce__]
let conditional_inv (r:ghostref bool) (p:slprop) =
      (fun (b:bool) ->
         ghost_pts_to r (half_perm full_perm) (hide b) `star`
         (if b then p else emp))

let ex_conditional_inv (r:ghostref bool) (p:slprop) =
    h_exists (conditional_inv r p)

let inv (p:slprop) = (r:ghostref bool & Steel.Memory.inv (ex_conditional_inv r p))

let name (#p:_) (i:inv p) = dsnd i
let gref (#p:_) (i:inv p) = dfst i

[@@__reduce__]
let active (#p:_) ([@@@smt_fallback]f:perm) (i:inv p) =
    ghost_pts_to (gref i) (half_perm f) (hide true)

assume
val admit_atomic (#a:_) (#u:_)
                 (#[@@@framing_implicit] p:pre_t)
                 (#[@@@framing_implicit] q:post_t a)
                 (_:unit)
  : SteelAtomicT a u unobservable p q

let new_inv (#u:_) (p:slprop)
  : SteelAtomicT (inv p) u unobservable p (active full_perm)
  = let r : ghostref bool = alloc_ghost (Ghost.hide true) in
    split_ghost r;
    A.intro_h_exists true (conditional_inv r p);
    let i = A.new_invariant u (ex_conditional_inv r p) in
    let tok = (| r, i |) in
    A.change_slprop (ghost_pts_to r (half_perm full_perm) (Ghost.hide true))
                    (active full_perm tok)
                    (fun _ -> ());
    tok

let share (#p:slprop) (#f:perm) (#u:_) (i:inv p)
  : SteelAtomicT unit u unobservable
    (active f i)
    (fun _ -> active (half_perm f) i `star` active (half_perm f) i)
  = split_ghost (gref i)

let gather (#p:slprop) (#f0 #f1:perm) (#u:_) (i:inv p)
  : SteelAtomicT unit u unobservable
    (active f0 i `star` active f1 i)
    (fun _ -> active (sum_perm f0 f1) i)
  = gather_ghost #_ #_ #(half_perm f0) #(half_perm f1) #(hide true) (gref i);
    A.change_slprop
      (ghost_pts_to (gref i) (sum_perm (half_perm f0) (half_perm f1)) (hide true))
      (ghost_pts_to (gref i) (half_perm (sum_perm f0 f1)) (hide true))
      (fun _ -> assert (FStar.Real.two == 2.0R))

assume
val drop (#u:_) (p:slprop)
  : SteelAtomicT unit u unobservable p (fun _ -> emp)

let iinv (#p:_) (i:inv p) : Steel.Memory.inv (ex_conditional_inv (gref i) p) = name i

let dispose' (#p:slprop) (#u:_) (i:inv p{not (name i `Set.mem` u)})
  : SteelAtomicT unit u unobservable
    (active full_perm i)
    (fun _ -> p)
  = let dispose_aux (r:ghostref bool) (_:unit)
     : SteelAtomicT unit (set_add (name i) u)  unobservable
       (ex_conditional_inv r p `star`
        ghost_pts_to r (half_perm full_perm) true)
       (fun _ ->
        ex_conditional_inv r p `star`
        p)
     = admit_atomic #unit #u ()
    in
    A.with_invariant #unit #(ghost_pts_to (gref i) (half_perm full_perm) true)
                           #(fun _ -> p)
                           #u
                           #unobservable
                           #(ex_conditional_inv (gref i) p)
                           (iinv i)
                           (dispose_aux (gref i))
