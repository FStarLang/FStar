module StackMachine

(* A port of http://adam.chlipala.net/cpdt/html/Cpdt.StackMachine.html *)

open FStar.List.Tot

(* Compiling arithmetic expressions to stack machine  *)

type binop : Type0 = | Plus | Times

type exp : Type0 =
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp

let add_nat (n1:nat) (n2:nat) : Tot nat = n1 + n2
let mul_nat (n1:nat) (n2:nat) : Tot nat = n1 `op_Multiply` n2
let eq_nat (n1:nat) (n2:nat) : Tot bool = n1 = n2
let eq_bool (b1:bool) (b2:bool) : Tot bool = b1 = b2
let lt_nat (n1:nat) (n2:nat) : Tot bool = n1 < n2

let binopDenote (b : binop) : nat -> nat -> Tot nat =
  match b with
    | Plus -> add_nat
    | Times -> mul_nat

let rec expDenote (e : exp) : Tot nat =
  match e with
    | Const n -> n
    | Binop b e1 e2 -> (binopDenote b) (expDenote e1) (expDenote e2)

type instr : Type0 =
| IConst : nat -> instr
| IBinop : binop -> instr

let prog = list instr
let stack = list nat

let instrDenote (i : instr) (s : stack) : Tot (option stack) =
  match i with
    | IConst n -> Some (n :: s)
    | IBinop b ->
      match s with
        | arg1 :: arg2 :: s' -> Some ((binopDenote b) arg1 arg2 :: s')
        | _ -> None

let rec progDenote (p : prog) (s : stack) : Tot (option stack) =
  match p with
    | [] -> Some s
    | i :: p' ->
      match instrDenote i s with
        | None -> None
        | Some s' -> progDenote p' s'

let rec compile (e : exp) : Tot prog =
  match e with
    | Const n -> [IConst n]
    | Binop b e1 e2 -> compile e2 @ compile e1 @ [IBinop b]

let rec app_assoc_reverse (#a:Type) (l : list a) (m : list a) (n : list a) :
    Lemma (requires True) (ensures ((l @ m) @ n == l @ m @ n)) [SMTPat ((l @ m) @ n)] =
  match l with
  | [] -> ()
  | _::l' -> app_assoc_reverse l' m n

let rec compile_correct' e p s :
    Lemma (progDenote (compile e @ p) s = progDenote p (expDenote e :: s)) =
  match e with
    | Const _ -> ()
    | Binop b e1 e2 -> compile_correct' e1 ([IBinop b] @ p) (expDenote e2 ::s);
                       compile_correct' e2 (compile e1 @ [IBinop b] @ p) s
       (* Finding the right arguments to pass to the recursive calls
          without an interactive mode seems tricky; I just copied them from Adam *)

let rec app_nil_end (#a : Type) (l : list a) :
    Lemma (requires True) (ensures (l == l @ [])) (decreases l) [SMTPat (l @ [])] =
  match l with
  | [] -> ()
  | _::l' -> app_nil_end l'

let compile_correct e : Lemma (progDenote (compile e) [] = Some [expDenote e])
  = compile_correct' e [] []

(* Typed Expressions *)

type typ : Type0 = | Nat | Bool

type tbinop : typ -> typ -> typ -> Type0 =
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : t:typ -> tbinop t t Bool
| TLt : tbinop Nat Nat Bool

type texp : typ -> Type0 =
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : #t1:typ -> #t2:typ -> #t:typ-> tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t

let typeDenote (t : typ) : Type0 =
  match t with
    | Nat -> nat
    | Bool -> bool

let tbinopDenote #arg1 #arg2 #res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> Tot (typeDenote res) =
  match b with
    | TPlus -> add_nat
    | TTimes -> mul_nat
    | TEq Nat -> eq_nat
    | TEq Bool -> eq_bool
    | TLt -> lt_nat

let rec texpDenote #t (e : texp t) : Tot (typeDenote t) (decreases e) =
  match e with
    | TNConst n -> n
    | TBConst b -> b
    | TBinop b e1 e2 -> (tbinopDenote b) (texpDenote e1) (texpDenote e2)

let tstack = list typ

type tinstr : tstack -> tstack -> Type0 =
| TiNConst : s:tstack -> nat -> tinstr s (Nat :: s)
| TiBConst : s:tstack -> bool -> tinstr s (Bool :: s)
| TiBinop : #arg1:typ -> #arg2:typ -> #res:typ -> #s:tstack ->
            tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s)

type tprog : tstack -> tstack -> Type0 =
| TNil : #s:tstack -> tprog s s
| TCons : #s1:tstack -> #s2:tstack -> #s3:tstack ->
          tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3

let rec vstack (ts : tstack) : Type0 =
  match ts with
    | [] -> unit
    | t :: ts' -> typeDenote t * vstack ts'

let rec tinstrDenote (#ts:tstack) (#ts':tstack)
                     (i : tinstr ts ts') (s:vstack ts) : Tot (vstack ts') =
  match i with
    | TiNConst _ n -> (n, s)
    | TiBConst _ b -> (b, s)
    | TiBinop #targ1 #targ2 #tres #tss b ->
      (* Take 1 *)
      (* let (arg1, (arg2, s')) = s in *)
      (*   ((tbinopDenote b) arg1 arg2, s')  *)
        (* Implicit pattern variables in (Prims.Mktuple2 arg1 (Prims.Mktuple2 arg2 s')) *)
        (* could not be resolved against expected type (StackMachine.vstack ts); *)
        (* Variables {?63598, ?63596, ?63406} were unresolved; please bind them explicitly *)

      (* Take 2 *)
      (* ((tbinopDenote b) (fst s) (fst (snd s)), (snd (snd s))) *)
        (* Subtyping check failed; expected type *)
        (*    (Prims.tuple2 (?63342 ts ts' i s uu___ uu___ uu___ uu___ b) *)
        (*                  (?63343 ts ts' i s uu___ uu___ uu___ uu___ b)); *)
        (* got type (StackMachine.vstack ts) *)

      (* Take 3: fully annotated *)
      let s' : typeDenote targ1 * (typeDenote targ2 * vstack tss) = s in
      let (arg1, (arg2, s'')) = s' in
        (((tbinopDenote b) arg1 arg2, s'') <: (typeDenote tres * vstack tss))

let rec tprogDenote #ts #ts' (p : tprog ts ts') (s:vstack ts) :
    Tot (vstack ts') (decreases p) =
  match p with
    | TNil -> s
    | TCons i p' -> tprogDenote p' (tinstrDenote i s)

let rec tconcat #ts #ts' #ts'' (p : tprog ts ts') (p' : tprog ts' ts'') :
    Tot (tprog ts ts'') (decreases p) =
  match p with
    | TNil -> p'
    | TCons i p1 -> TCons i (tconcat p1 p')

let rec tcompile #t (e : texp t) (ts : tstack) : Tot (tprog ts (t :: ts)) (decreases e) =
  match e with
    | TNConst n -> TCons (TiNConst _ n) TNil
    | TBConst b -> TCons (TiBConst _ b) TNil
    | TBinop #t1 #t2 #t b e1 e2 ->
      tconcat (tcompile e2 ts)
        (tconcat (tcompile e1 (t1 :: ts)) (TCons (TiBinop b) TNil))
        (* Coq can even infer the ts and (t1::ts) arguments if they
           are replaced with _, but F* is not that magic at the moment.
           In fact it fails with a quite silly error message.
./StackMachine.fst(175,27-175,28): Failed to verify implicit argument: Subtyping check failed; expected type (ts#82697:StackMachine.tstack{(Prims.precedes (Prims.LexCons e2 Prims.LexTop) (Prims.LexCons e Prims.LexTop))}); got type StackMachine.tstack
./StackMachine.fst(176,30-176,31): Failed to verify implicit argument: Subtyping check failed; expected type (ts#82697:StackMachine.tstack{(Prims.precedes (Prims.LexCons e1 Prims.LexTop) (Prims.LexCons e Prims.LexTop))}); got type (Prims.list StackMachine.typ)  *)

#reset-options "--z3rlimit 10"

let rec tconcat_correct #ts #ts' #ts''
                       (p : tprog ts ts') (p' : tprog ts' ts'') (s : vstack ts) :
    Lemma (requires True)
          (ensures (tprogDenote (tconcat p p') s == tprogDenote p' (tprogDenote p s)))
          (decreases p) [SMTPat (tprogDenote (tconcat p p') s)] =
  match p with
  | TNil -> ()
  | TCons t pp -> tconcat_correct pp p' (tinstrDenote t s)
                  (* again just taking Adam's instantiations *)

let rec tcompile_correct' #t (e : texp t) ts (s : vstack ts) :
    Lemma (requires True)
          (ensures (tprogDenote (tcompile e ts) s == (texpDenote e, s)))
          (decreases e) =
  match e with
    | TNConst _ -> ()
    | TBConst _ -> ()
    | TBinop #t1 #t2 b e1 e2 -> 
      tcompile_correct' e1 (t2 :: ts) (texpDenote e2, s);
      tcompile_correct' e2 ts s;
      let p1 = tcompile e1 (t1::ts) in
      let p = TCons (TiBinop b) TNil in
      tconcat_correct p1 p (texpDenote e2, s) //NS: added this explicitly after #1028
      (* again just taking Adam's instantiations *)

let tcompile_correct #t (e : texp t) :
    Lemma (tprogDenote (tcompile e []) () == (texpDenote e, ())) =
  tcompile_correct' e [] ()
