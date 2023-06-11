module LListReverse
open Steel.ST.GenElim
open Steel.ST.Reference
open Steel.ST.Loops

module U64 = FStar.UInt64

let main () = C.EXIT_SUCCESS // dummy for compilation

noeq
type llist_cell = {
  value: U64.t;
  next: ref llist_cell;
}

[@@__reduce__]
let llist_nil
  (p: ref llist_cell)
: Tot vprop
= pure (p == null)

[@@__reduce__]
let llist_cons
  (a: U64.t)
  (llist: (ref llist_cell -> Tot vprop))
  (p: ref llist_cell)
: Tot vprop
= exists_ (fun c ->
    pts_to p full_perm c `star`
    pure (c.value == a) `star`
    llist c.next
  )

let rec llist
  (l: Ghost.erased (list U64.t))
: Tot (ref llist_cell -> vprop)
  (decreases Ghost.reveal l)
= match Ghost.reveal l with
  | [] -> llist_nil
  | a :: q -> llist_cons a (llist q)

let llist_nil_is_null
  (#opened: _)
  (l: Ghost.erased (list U64.t))
  (p: ref llist_cell)
: STGhost unit opened
    (llist l p)
    (fun _ -> llist l p)
    True
    (fun _ -> (p == null <==> Nil? l))
= if Nil? l
  then begin
    rewrite (llist l p) (llist_nil p);
    let _ = gen_elim () in
    rewrite (llist_nil p) (llist l p)
  end else begin
    let a :: q = Ghost.reveal l in
    rewrite (llist l p) (llist_cons a (llist q) p);
    let _ = gen_elim () in
    pts_to_not_null p;
    rewrite (llist_cons a (llist q) p) (llist l p)
  end

let pop
  (#l: Ghost.erased (list U64.t))
  (p: ref llist_cell { Cons? l })
: STT (ref llist_cell)
    (llist l p)
    (fun p' -> exists_ (fun x -> pts_to p full_perm x `star` llist (List.Tot.tl l) p' `star` pure (x.value == List.Tot.hd l)))
= rewrite (llist l p) (llist_cons (List.Tot.hd l) (llist (List.Tot.tl l)) p);
  let _ = gen_elim () in
//  let p' = (read p).next in // FIXME: "Effects STBase and Tot cannot be composed"
  let x = read p in
  let p' = x.next in
  vpattern_rewrite (llist _) p';
  return p'

let push
  (#l': Ghost.erased (list U64.t))
  (#x: Ghost.erased llist_cell)
  (p: ref llist_cell)
  (p': ref llist_cell)
: STT unit
    (llist l' p' `star` pts_to p full_perm x)
    (fun p' -> llist (x.value :: l') p)
= 
//  write p ({ read p with next = p' }); // weird Steel error
  let x_ = read p in
  write p ({ x_ with next = p' });
  let x' = vpattern_replace (pts_to p full_perm) in
  vpattern_rewrite (llist _) x'.next;
  rewrite (llist_cons x.value (llist l') p) (llist (x.value :: l') p)

noextract
let llist_reverse_invariant_prop
  (l: list U64.t)
  (done todo: list U64.t)
  (cont: bool)
: GTot prop
=
    l == List.Tot.append (List.Tot.rev done) todo /\
    cont == Cons? todo

[@@erasable]
noeq
type llist_reverse_invariant_t (l: list U64.t) (cont: bool) = {
  pdone: ref llist_cell;
  done: list U64.t;
  ptodo: ref llist_cell;
  todo: list U64.t;
  prf: squash (llist_reverse_invariant_prop l done todo cont);
}

[@@__reduce__]
let llist_reverse_invariant_body
  (ppdone: ref (ref llist_cell))
  (pptodo: ref (ref llist_cell))
  (pdone: ref llist_cell)
  (done: Ghost.erased (list U64.t))
  (ptodo: ref llist_cell)
  (todo: Ghost.erased (list U64.t))
: Tot vprop
= pts_to ppdone full_perm pdone `star` llist done pdone `star`
  pts_to pptodo full_perm ptodo `star` llist todo ptodo

[@@__reduce__]
let llist_reverse_invariant0
  (l: Ghost.erased (list U64.t))
  (ppdone: ref (ref llist_cell))
  (pptodo: ref (ref llist_cell))
  (cont: bool)
: Tot vprop
= exists_ (fun (x: llist_reverse_invariant_t l cont) -> llist_reverse_invariant_body ppdone pptodo x.pdone x.done x.ptodo x.todo)

let llist_reverse_invariant
  (l: Ghost.erased (list U64.t))
  (ppdone: ref (ref llist_cell))
  (pptodo: ref (ref llist_cell))
  (cont: bool)
: Tot vprop
= llist_reverse_invariant0 l ppdone pptodo cont

let intro_llist_reverse_invariant
  (#opened: _)
  (l: Ghost.erased (list U64.t))
  (ppdone: ref (ref llist_cell))
  (pptodo: ref (ref llist_cell))
  (cont: bool)
  (pdone: ref llist_cell)
  (done: Ghost.erased (list U64.t))
  (ptodo: ref llist_cell)
  (todo: Ghost.erased (list U64.t))
: STGhost unit opened
    (llist_reverse_invariant_body ppdone pptodo pdone done ptodo todo)
    (fun _ -> llist_reverse_invariant l ppdone pptodo cont)
    (llist_reverse_invariant_prop l done todo cont)
    (fun _ -> True)
= let x : llist_reverse_invariant_t l cont = {
    pdone = pdone;
    done = done;
    ptodo = ptodo;
    todo = todo;
    prf = ();
  }
  in
  rewrite
    (llist_reverse_invariant_body ppdone pptodo pdone done ptodo todo)
    (llist_reverse_invariant_body ppdone pptodo x.pdone x.done x.ptodo x.todo);
  rewrite
    (llist_reverse_invariant0 l ppdone pptodo cont)
    (llist_reverse_invariant l ppdone pptodo cont)

let elim_llist_reverse_invariant
  (#opened: _)
  (l: Ghost.erased (list U64.t))
  (ppdone: ref (ref llist_cell))
  (pptodo: ref (ref llist_cell))
  (cont: bool)
: STGhostT (llist_reverse_invariant_t l cont) opened
    (llist_reverse_invariant l ppdone pptodo cont)
    (fun x -> llist_reverse_invariant_body ppdone pptodo x.pdone x.done x.ptodo x.todo)
= let x = elim_exists () in
  x

let list_rev_transfer
  (ll: list U64.t) (x: U64.t) (lr: list U64.t)
: Lemma
  (List.Tot.append (List.Tot.rev ll) (x :: lr) == List.Tot.append (List.Tot.rev (x :: ll)) lr)
= List.Tot.rev_rev' (x :: ll);
  List.Tot.rev_rev' ll;
  List.Tot.append_assoc (List.Tot.rev ll) [x] lr

let list_rev_done
  (l1 l2: list U64.t)
: Lemma
  (requires (
    l1 == List.Tot.append (List.Tot.rev l2) []
  ))
  (ensures (l2 == List.Tot.rev l1))
= List.Tot.append_l_nil (List.Tot.rev l2);
  List.Tot.rev_involutive l2

let llist_reverse
  (l: Ghost.erased (list U64.t))
  (p: ref llist_cell)
: STT (ref llist_cell)
    (llist l p)
    (fun p' -> llist (List.Tot.rev l) p')
= with_local (null #llist_cell) (fun ppdone ->
  with_local p (fun pptodo ->
    rewrite (llist_nil null) (llist [] null);
    intro_llist_reverse_invariant l ppdone pptodo (Cons? l) _ [] _ l;
    Steel.ST.Loops.while_loop
      (llist_reverse_invariant l ppdone pptodo)
      (fun _ ->
        let gcont = elim_exists () in
        let x = elim_llist_reverse_invariant _ _ _ _ in
        llist_nil_is_null x.todo x.ptodo;
        let ptodo = read pptodo in
        let res = not (is_null ptodo) in
        intro_llist_reverse_invariant _ _ _ res x.pdone x.done x.ptodo x.todo;
        return res
      )
      (fun _ ->
        let x = elim_llist_reverse_invariant _ _ _ _ in
        let ptodo = read pptodo in
        vpattern_rewrite (llist x.todo) ptodo;
        let ptodo_next = pop ptodo in
        let _ = gen_elim () in
        let pdone = read ppdone in
        vpattern_rewrite (llist x.done) pdone;
        push ptodo pdone;
        list_rev_transfer x.done (List.Tot.hd x.todo) (List.Tot.tl x.todo);
        write pptodo ptodo_next;
        write ppdone ptodo;
        intro_llist_reverse_invariant _ _ _ (Cons? (List.Tot.tl x.todo)) ptodo _ ptodo_next _;
        noop ()
      );
    let x = elim_llist_reverse_invariant _ _ _ _ in
    list_rev_done l x.done;
    let pdone = read ppdone in
    rewrite (llist x.todo _) (llist_nil x.ptodo);
    rewrite (llist _ _) (llist (List.Tot.rev l) pdone);
    let _ = gen_elim () in
    return pdone
  ))
