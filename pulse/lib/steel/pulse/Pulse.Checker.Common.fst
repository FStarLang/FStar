module Pulse.Checker.Common
module T = FStar.Tactics
module Metatheory = Pulse.Typing.Metatheory

let post_hint_typing g p x = {
  ty_typing=admit();
  post_typing=admit()
}

let intro_post_hint g ret_ty_opt post =
  let x = fresh g in
  if x `Set.mem` freevars post
  then T.fail "Unexpected variable clash in intro_post_hint"
  else (
    let ret_ty = 
      match ret_ty_opt with
      | None -> Tm_FStar RT.unit_ty FStar.Range.range_0
      | Some t -> t
    in
    admit()
  )

let post_typing_as_abstraction (#g:env) (#x:var) (#ty:term) (#t:term { Metatheory.fresh_wrt x g (freevars t) })
                               (_:tot_typing (extend x (Inl ty) g) (open_term t x) Tm_VProp)
  : RT.tot_typing (elab_env g) (mk_abs ty t) (mk_arrow ty Tm_VProp)                                 
  = admit()

let post_hint_from_comp_typing #g #c ct = 
  let st_comp_typing = Metatheory.comp_typing_inversion ct in
  let (| ty_typing, pre_typing, x, post_typing |) = Metatheory.st_comp_typing_inversion st_comp_typing in
  let p : post_hint_t = 
    { g; ret_ty = comp_res c; u=comp_u c; 
      ty_typing=ty_typing;
      post=comp_post c;
      post_typing=post_typing_as_abstraction post_typing }
  in
  extends_env_refl g;
  p
