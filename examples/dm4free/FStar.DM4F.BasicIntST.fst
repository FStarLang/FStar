module FStar.DM4F.BasicIntST

(**********************************************************
 * A very simple example with a single integer as the state
 *
 * The main interesting bit is proving some identities about
 * reify/bind in various styles
 *
 **********************************************************)

(* The underlying representation type *)
let st (a:Type) = int -> M (a * int)

(* Monad definition *)
let return_st (a:Type) (x:a) : st a = fun s0 -> x, s0

let bind_st (a:Type) (b:Type) (f:st a) (g:a -> st b) : st b
  = fun (s0:int) -> let (x,s) = f s0 in g x s

(* Actions *)
let get () : st int = fun s0 -> s0, s0

let put (x:int) : st unit = fun _ -> (), x

(*
 * Do the DM4F work. Note that the heap type is a parameter
 * of the resulting effect.
 *)
total reifiable reflectable new_effect {
  STATE : a:Type -> Effect
  with repr     = st
     ; bind     = bind_st
     ; return   = return_st
     ; get      = get
     ; put      = put
}


open FStar.Tactics


//Re-define bind_elab with implicit parameters for easier use
let bind_elab #a #b #f_w ($f:_) #g_w ($g:_) = STATE?.bind_elab a b f_w f g_w g
assume val range0: range
let bind_wp = STATE?.bind_wp range0

let reified_st a (wp:STATE?.wp a) = s0:int -> PURE (a * int) (wp s0)

let monotonic #a (wp:STATE?.wp a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2} (forall x. p1 x ==> p2 x) ==> wp s p1 ==> wp s p2

let test_bind_elab #a #b
    #f_w (f:reified_st a f_w)
    #g_w (g: (x:a -> reified_st b (g_w x)))
    : reified_st b (bind_wp a b f_w g_w)
    = fun s0 ->
        assume (monotonic f_w);
        let x, s1 = f s0 in
        assume (monotonic (g_w x));
        g x s1

let test1 (s0:int) (v:int) =
  assert ((reify (let _ = STATE?.put v in
                   STATE?.put v) s0 ==
           bind_elab (reify (STATE?.put v))
                     (fun _ -> reify (STATE?.put v)) s0))

let test2 (s0:int) (v:int) =
  assert ((reify (let _ = STATE?.put v in
                   STATE?.put v) s0 ==
                   bind_elab (reify (STATE?.put v))
                             (fun _ -> reify (STATE?.put v)) s0))
      by (dump "start"; norm [reify_; delta_only [`%bind_elab; `%STATE?.bind_elab]]; trefl())

let st_thunk a wp = unit -> STATE a wp

let y = STATE?.bind_wp


let reify_bind_commutes
          (#a #b : _)
          (#wp1 : _) (c1:st_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> st_thunk b (wp2 x)))
          (s0:_{(monotonic wp1 /\
                (forall x. monotonic (wp2 x)) /\
                bind_wp _ _ wp1 wp2 s0 (fun _ -> True))})
     = reify (let x = c1 () in c2 x ()) s0 ==
       bind_elab (reify (c1 ()))
                 (fun x -> reify (c2 x ())) s0


let commutation_lemma
          (#a #b : _)
          (#wp1 : _) (c1:st_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> st_thunk b (wp2 x))) (s0:_)
    : Lemma
         (requires (monotonic wp1 /\
                    (forall x. monotonic (wp2 x)) /\
                    STATE?.bind_wp range0 _ _ wp1 wp2 s0 (fun _ -> True)))
         (ensures (reify_bind_commutes c1 c2 s0))
    = assert (reify_bind_commutes c1 c2 s0)
          by (dump "start";
              norm [reify_; delta_only [`%bind_elab; `%STATE?.bind_elab; `%reify_bind_commutes]];
              dump "after norm";
              trefl())

let commutation_lemma_alt
          (#a #b : _)
          (#wp1 : _) (c1:st_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> st_thunk b (wp2 x)))
          (s0:_{(monotonic wp1 /\
                (forall x. monotonic (wp2 x)) /\
                STATE?.bind_wp range0 _ _ wp1 wp2 s0 (fun _ -> True))})
    = assert (reify_bind_commutes c1 c2 s0) //inlining reify_bind_commutes here does not work
          by (dump "start";
              norm [reify_; delta_only [`%bind_elab; `%STATE?.bind_elab; `%reify_bind_commutes]];
              dump "after norm";
              trefl())
