module ListExample

open Steel.C.PCM
open Steel.C.Ref

open Steel.Effect
module A = Steel.Effect.Atomic

open FStar.PCM.POD
open ListNode

/// void mk_figure_eight(struct node *p, struct node *q) {
///   p->next = q;
///   q->next = p;
/// }

let ptr (p: ref node node_pcm)
: Ghost.erased (option (ref' node node))
= Ghost.hide (Some (|Ghost.hide node_pcm, p|))

let ptr' (p: ref node node_pcm)
: option (ref' node node)
= Some (|Ghost.hide node_pcm, p|)

let nullptr: Ghost.erased (option (ref' node node)) = Ghost.hide None

val mk_figure_eight_step_one
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (i j: Ghost.erased int')
: SteelT (r:ref node (pod_pcm (option (ref' node node))){r == ref_focus p _next})
    (p `pts_to` mk_node (some i) (some nullptr))
    (fun r ->
      (p `pts_to` mk_node (some i) none) `star`
      (r `pts_to` some nullptr))

let mk_figure_eight_step_one p q i j =
  addr_of_next #node #(some i) #(some nullptr) p

val mk_figure_eight_step_two
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (i j: Ghost.erased int')
: SteelT (r:ref node (pod_pcm (option (ref' node node))){r == ref_focus q _next})
    (q `pts_to` mk_node (some j) (some nullptr))
    (fun r ->
      (q `pts_to` mk_node (some j) none) `star`
      (r `pts_to` some nullptr))

let mk_figure_eight_step_two p q i j =
  addr_of_next #node #(some j) #(some nullptr) q

val mk_figure_eight_step_three
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (p_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus p _next}))
  (q_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus q _next}))
  (i j: Ghost.erased int')
: SteelT unit
    (p_next `pts_to` some nullptr)
    (fun _ -> p_next `pts_to` some (ptr q))

let mk_figure_eight_step_three p q p_next q_next i j =
  pod_write p_next (ptr' q)

val mk_figure_eight_step_four
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (p_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus p _next}))
  (q_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus q _next}))
  (i j: Ghost.erased int')
: SteelT unit
    (q_next `pts_to` some nullptr)
    (fun _ -> q_next `pts_to` some (ptr p))

let mk_figure_eight_step_four p q p_next q_next i j =
  pod_write q_next (ptr' p)

val mk_figure_eight_step_five
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (p_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus p _next}))
  (q_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus q _next}))
  (i j: Ghost.erased int')
: SteelT unit
    ((p `pts_to` mk_node (some i) none) `star`
     (p_next `pts_to` some (ptr q)))
    (fun _ -> p `pts_to` mk_node (some i) (some (ptr q)))

let mk_figure_eight_step_five p q p_next q_next i j =
  unaddr_of_next p p_next

val mk_figure_eight_step_six
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (p_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus p _next}))
  (q_next:(r:ref node (pod_pcm (option (ref' node node))){r == ref_focus q _next}))
  (i j: Ghost.erased int')
: SteelT unit
    ((q `pts_to` mk_node (some j) none) `star`
     (q_next `pts_to` some (ptr p)))
    (fun _ -> q `pts_to` mk_node (some j) (some (ptr p)))

let mk_figure_eight_step_six p q p_next q_next i j =
  unaddr_of_next q q_next

val mk_figure_eight_verbose
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (i j: Ghost.erased int')
: SteelT unit
    ((p `pts_to` mk_node (some i) (some nullptr)) `star`
     (q `pts_to` mk_node (some j) (some nullptr)))
    (fun _ ->
      (p `pts_to` mk_node (some i) (some (ptr q))) `star`
      (q `pts_to` mk_node (some j) (some (ptr p))))

let mk_figure_eight_verbose p q i j =
  let p_next = mk_figure_eight_step_one p q i j in
  let q_next = mk_figure_eight_step_two p q i j in
  mk_figure_eight_step_three p q p_next q_next i j;
  mk_figure_eight_step_four p q p_next q_next i j;
  mk_figure_eight_step_five p q p_next q_next i j;
  mk_figure_eight_step_six p q p_next q_next i j;
  A.return ()

val mk_figure_eight
  (p: ref node node_pcm)
  (q: ref node node_pcm)
  (i j: Ghost.erased int')
: SteelT unit
    ((p `pts_to` mk_node (some i) (some nullptr)) `star`
     (q `pts_to` mk_node (some j) (some nullptr)))
    (fun _ ->
      (p `pts_to` mk_node (some i) (some (ptr q))) `star`
      (q `pts_to` mk_node (some j) (some (ptr p))))

#push-options "--query_stats --profile ListExample --profile_component FStar"

let mk_figure_eight p q i j =
  let p_next = addr_of_next p in
  let q_next = addr_of_next q in
  p_next `pod_write` ptr' q;
  q_next `pod_write` ptr' p;
  unaddr_of_next p p_next;
  unaddr_of_next q q_next;
  A.return ()
