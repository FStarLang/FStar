module Phase2CoreEqUnderAbs

(* Relating [v p1] to [v p2] equates two slprops with a function literal
   ([exists* y. ...]) inside: rather than the whole equation, which needs
   extensionality, Core may prove their arguments equal, under the binder. *)
assume val slp : Type u#1
assume val star (a b:slp) : slp
assume val ex (#a:Type) (f: a -> slp) : slp
assume val pure (p:prop) : slp
assume val pts (x:int) : slp
assume val st (post: bool -> slp) : Type0
let vp (p:int->int) (x:int) (r:bool) : bool = r = (p x = 0)
let v (p:int -> int) = x:int -> st (fun r -> star (pts x) (ex (fun (y:int) -> star (pts y) (pure (vp p x r)))))
let ext (p1:int->int) (f: v p1) (p2:int->int{forall x. p1 x == p2 x}) : v p2 = f
