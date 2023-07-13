module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

let admit_st_comp_typing (g:env) (st:st_comp) 
  : st_comp_typing g st
  = admit(); 
    STC g st (fresh g) (admit()) (admit()) (admit())

let admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  = match c with
    | C_ST st ->
      CT_ST g st (admit_st_comp_typing g st)
    | C_STAtomic inames st ->
      CT_STAtomic g inames st (admit()) (admit_st_comp_typing g st)
    | C_STGhost inames st ->
      CT_STGhost g inames st (admit()) (admit_st_comp_typing g st)      

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = admit_comp_typing g c
    
let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f tm_vprop)
  : comp_typing_u g (add_frame c f)
  = admit_comp_typing _ _

let comp_typing_inversion #g #c ct = 
  match ct with
  | CT_ST _ _ st
  | CT_STAtomic _ _ _ _ st 
  | CT_STGhost _ _ _ _ st   -> st

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  admit(), admit(), (fun _ -> admit())

let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  let STC g st x ty pre post = ct in
  (| ty, pre, x, post |)

let tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_vprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_vprop
  = admit(), admit()

let tot_typing_weakening #g #t #ty x b d = admit()

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_vprop)
   : tot_typing g p (tm_fstar FStar.Reflection.Typing.tm_prop Range.range_0)
   = admit ()

let rec st_typing_weakening g g' t c d g1
  : Tot (st_typing (push_env (push_env g g1) g') t c)
        (decreases d) =
  
  match d with
  | T_Abs _ _ _ _ _ _ _ _ _ ->
    // T_Abs is used only at the top, should not come up
    magic ()

  | T_STApp _ head ty q res arg _ _ ->
    T_STApp _ head ty q res arg (magic ()) (magic ())

  | T_Return _ c use_eq u t e post x_old _ _ _ ->
    let x = fresh (push_env (push_env g g1) g') in
    assume (~ (x `Set.mem` freevars post));
    assume (comp_return c use_eq u t e post x_old ==
            comp_return c use_eq u t e post x);
    T_Return _ c use_eq u t e post x (magic ()) (magic ()) (magic ())

  | T_Lift _ e c1 c2 d_c1 d_lift ->
    

  | _ -> admit ()
  
