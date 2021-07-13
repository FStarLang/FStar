module FStar.PCM.Extras

open FStar.PCM
open FStar.FunctionalExtensionality
open FStar.Classical
open Lens

(** PCM morphisms *)

let pcm_morphism_id #a #p = {
  f_refine = (fun _ -> ());
  f_one = (fun _ -> ());
  f_op = (fun _ _ -> ());
}

let pcm_morphism_comp #a #b #c #p #q #r #f #g mf mg = {
  f_refine = (fun x -> mg.f_refine x; mf.f_refine (g x));
  f_one = (fun () -> mg.f_one (); mf.f_one ());
  f_op = (fun x y -> mg.f_op x y; mf.f_op (g x) (g y));
}

let compatible_pcm_morphism #a #b #p #q f m x y =
  compatible_elim p x y (compatible q (f x) (f y)) (fun frame_x ->
  let _ = m.f_op frame_x x in
  compatible_intro q (f x) (f y) (f frame_x))

(** Refinements *)

let pcm_refinement'_comp_one #a #p re x y =
  p.is_unit x;
  p.assoc_r x (one p) y;
  re.f_closed_comp (one p) y

let pcm_refinement'_compatible_closed #a #p re x y =
  let p' = refined_pcm' re in
  compatible_elim p x y (re.f y) (fun frame ->
   re.f_closed_comp x frame; p.comm frame x);
  compatible_elim p x y (compatible p' x y) (fun frame_x ->
    pcm_refinement'_comp_one re x frame_x;
    let frame = op p (one p) frame_x in
    p.is_unit x;
    p.comm x frame_x;
    p.assoc x (one p) frame_x;
    p.comm x (op p (one p) frame_x);
    compatible_intro p' x y (op p (one p) frame_x))

(** PCM lenses *)

let pcm_lens_compatible_get #a #b #p #q l x y =
  compatible_pcm_morphism l.l.get l.get_morphism x y
    
let pcm_lens_frame_pres #a #b #p #q l s v f =
  frame_pres_intro p (upd l f) s (put l v s) (fun full ->
    let _ = l.get_morphism.f_refine in
    pcm_lens_compatible_get l s full;
    l.put_morphism.f_refine (f (get l full), full);
    let goal = frame_pres_on p (upd l f) s (put l v s) full in
    compatible_elim p s full goal (fun frame_s ->
    compatible_elim q v (f (get l full)) goal (fun frame_v ->
    let frame_vs: a = put l frame_v frame_s in
    l.put_morphism.f_op (v, s) (frame_v, frame_s);
    p.comm frame_vs (put l v s);
    q.comm v frame_v;
    p.comm s frame_s;
    compatible_intro p (put l v s) (upd l f full) frame_vs;
    let aux (frame:a{composable p s frame})
    : Lemma (composable p (put l v s) frame /\
             (op p s frame == full ==> op p (put l v s) frame == upd l f full))
    = l.get_morphism.f_op s frame;
      l.put_morphism.f_op (v, s) (get l frame, frame);
      let aux ()
      : Lemma (requires op p s frame == full) 
              (ensures op p (put l v s) frame == upd l f full)
      = () in ()
    in FStar.Classical.forall_intro aux)))

(*
(** Refinement of union to the kth case *)

let case_unrefinement (#a:eqtype) #b (p:(k:a -> refined_one_pcm (b k))) (k:a)
: pcm_unrefinement (case_refinement' p k)
= fun kx ky f kv ->
  let p' = refined_pcm' (case_refinement' p k) in
  let p = union_pcm p in
  match kv with
  | Some (|k', v|) ->
    if k = k' then begin
      let _ = Ghost.hide (
        let Some (|k, x|) = Ghost.reveal kx in
        let goal = compatible p' kx kv in
        compatible_elim p kx kv goal (fun kx_frame -> match kx_frame with
          | Some (|_, frame_x|) -> compatible_intro p' kx kv (Some (|k, frame_x|))
          | None -> compatible_refl p' kx))
      in
      let kw = f kv in
      let aux (frame:union b{composable p kx frame})
      : Lemma (composable p ky frame /\
               (op p kx frame == Some (|k, v|) ==>
                op p ky frame == f (Some (|k, v|))))
      = let Some (|_, w|) = f (Some (|k, v|)) in
        match frame with
        | Some (|frame_k, frame_v|) -> assert (composable p' kx frame)
        | None ->
          p'.is_unit kx;
          assert (composable p' kx (one p'));
          p'.is_unit ky
      in FStar.Classical.forall_intro aux;
      kw
    end else None
  | _ -> None
*)

let conj_unrefinement (#p: refined_one_pcm 'a)
  (re1: pcm_refinement' p) (re2: pcm_refinement' (refined_pcm' re1))
  (h1: pcm_unrefinement re1) (h2: pcm_unrefinement re2)
: pcm_unrefinement (conj_refinement #'a re1 re2)
= fun x y ->
  h1 (Ghost.reveal x) (Ghost.reveal y) `compose`
  h2 (Ghost.reveal x) (Ghost.reveal y) `compose`
  upd_across_pcm_iso (pcm_refinement'_conj_iso p re1 re2) x y

let extend_unrefinement (#p: refined_one_pcm 'a) (#q: refined_one_pcm 'b)
  (l: pcm_lens p q) (re: pcm_refinement' q) (u: pcm_unrefinement re)
: pcm_unrefinement (extend_refinement l re)
= fun x y f v ->
  let re' = extend_refinement l re in
  let p' = refined_pcm' re' in
  pcm_refinement'_compatible_closed re' x v;
  pcm_lens_compatible_get l x v;
  let w = f v in
  let aux (frame:'a{composable p x frame})
  : Lemma (composable p y frame /\ (op p x frame == v ==> op p y frame == w))
  = pcm_refinement'_comp_one re' x frame;
    let frame' = op p (one p) frame in
    p.assoc y (one p) frame;
    p.is_unit y;
    p.assoc x (one p) frame;
    p.is_unit x
  in FStar.Classical.forall_intro aux;
  w
