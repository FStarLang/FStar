module Pulse.Typing.FV
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Soundness.Common

let vars_of_rt_env (g:R.env) = Set.intension (fun x -> Some? (RT.lookup_bvar g x))
  

assume
val refl_typing_freevars (#g:R.env) (#e:R.term) (#t:R.term) 
                         (_:RT.typing g e t)
                         (x:R.var)
  : Lemma 
    (requires x `Set.mem` RT.freevars t \/
              x `Set.mem` RT.freevars e)
    (ensures Some? (RT.lookup_bvar g x))

assume
val elab_freevars_inverse (e:pure_term)
  : Lemma 
    (ensures RT.freevars (elab_pure e) == freevars e)

let rec src_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
                            (d:src_typing f g t c)
                            (x:var)
  : Lemma 
    (requires x `Set.mem` freevars t \/
              x `Set.mem` freevars_comp c)
    (ensures Some? (lookup g x))
  = admit()
//   = match d with
//     | T_Tot _g e t dt ->
//       elab_freevars_inverse e;
//       elab_freevars_inverse t;      
//       refl_typing_freevars dt x

//     | T_Abs _g _pp x _q ty _u body c (E dt) db ->
//       src_typing_freevars dt;
//       src_typing_freevars db;      
    

//     | T_STApp _ _ _ _ _ res arg st (E at) ->
//       src_typing_ln st;
//       src_typing_ln at;
//       open_comp_ln'_inv res arg 0

//     | T_Return _ _ _ _ (E tt) _
//     | T_ReturnNoEq _ _ _ _ tt _ ->
//       src_typing_ln tt

//     | T_Lift _ _ _ _ d1 l ->
//       src_typing_ln d1;
//       lift_comp_ln l

//     | T_Bind _ _ e2 _ _ x _ d1 (E dc1) d2 bc ->
//       src_typing_ln d1;
//       src_typing_ln dc1;
//       src_typing_ln d2;
//       open_term_ln e2 x;
//       bind_comp_ln bc

//     | T_If _ _ _ _ _ _ (E tb) d1 d2 ->
//       src_typing_ln tb;
//       src_typing_ln d1;
//       src_typing_ln d2

//     | T_Frame _ _ _ _ (E df) dc ->
//       src_typing_ln df;
//       src_typing_ln dc

//     | T_ElimExists _ _ _ _ (E dt) (E dv) ->
//       src_typing_ln dt;
//       src_typing_ln dv

//     | T_IntroExists _ u t p e (E dt) (E dv) (E dw) ->
//       src_typing_ln dt;
//       src_typing_ln dv;
//       src_typing_ln dw;
//       open_term_ln'_inv p e 0
      
//     | T_Equiv _ _ _ _ d2 deq ->
//       src_typing_ln d2;
//       st_equiv_ln deq
// #pop-options


// assume
// val well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:RT.typing g e t)
//   : Lemma (ensures RT.ln e /\ RT.ln t)

// assume
// val elab_ln_inverse (e:pure_term)
//   : Lemma 
//     (requires RT.ln (elab_pure e))
//     (ensures ln e)

// let rec src_typing_freevars (#f:_) (#g:_) (#t:_) (#c:_)
//                             (d:src_typing f g t c)
//                             (x:var)
//   : Lemma 
//     (requires x `Set.mem` freevars t \/
//               x `Set.mem` freevars_comp c)
//     (ensures Some? (lookup g x))
//   = match d with

