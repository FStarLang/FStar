module AlgebraicEffects.WithPaths

include FStar.List.Tot

(* operation symbols *)

type op = 
  | Op : name:string -> arity:nat -> op

(* signatures *)

let sig = l:list op{forall s n . count (Op s n) l <= 1}

(* computation trees *)

type comp_tree (vars:Type0) = 
  | Leaf : vars -> comp_tree vars
  | Node : o:op -> args:list (comp_tree vars){length args = Op?.arity o} -> comp_tree vars

(* equations *)

type equation vars =
  | Eq : left:comp_tree vars -> right:comp_tree vars -> equation vars

let equations vars = list (equation vars)

let in_equations #vars (e:equation vars) (eqs:equations vars) =
  fold_left (fun x y -> x \/ y) False (map (fun e' -> e == e') eqs)

(* paths *)

type path (vars:Type0) = 
  | Ret : vars -> path vars
  | Bot : path vars
  | OpZ : o:op{Op?.arity o = 0} -> path vars
  | OpN : o:op -> n:nat{n >= 1 /\ n <= Op?.arity o} -> path vars -> path vars

let rec path_subst #vars1 #vars2 (p1:path vars1) (p2:vars1 -> path vars2) = 
  match p1 with
  | Ret v     -> p2 v
  | Bot       -> Bot
  | OpZ o     -> OpZ o
  | OpN o n p -> OpN o n (path_subst p p2)

let rec path_in_tree #vars (p:path vars) (t:comp_tree vars) = 
  match p with
  | Ret v -> (match t with 
              | Leaf w   -> v == w
              | Node _ _ -> False)
  | Bot -> False
  | OpZ o -> (match t with
              | Leaf _       -> False
              | Node o' args -> o = o' /\ (match args with
                                          | []   -> True
                                          | _::_ -> False))
  | OpN o n p' -> (match t with 
                   | Leaf _       -> False
                   | Node o' args -> o = o' /\ (match (nth args (n - 1)) with
                                               | None    -> False
                                               | Some t' -> path_in_tree p' t'))

let rec path_ends_with #vars (p:path vars) =
  match p with
  | Ret v -> Some v
  | Bot   -> None
  | OpZ _ -> None
  | OpN _ _ p -> path_ends_with p

let compatible_paths #vars (p1:path vars) (p2:path vars) =
  match path_ends_with p1 with
  | None   -> (match path_ends_with p2 with
               | None   -> True
               | Some _ -> False)
  | Some v -> (match path_ends_with p2 with
               | None -> False
               | Some w -> v == w)

let rec has_compatible_paths_with #vars (t:comp_tree vars) (p:path vars{Some? (path_ends_with p)}) = 
  match t with
  | Leaf v      -> (match (path_ends_with p) with
                    | Some w -> v == w)
  | Node o args -> if (Op?.arity o = 0) then True 
                                        else fold_left (fun x y -> x \/ y) False 
                                                       (map (fun t' -> assume (t' << t) (* for time being *); has_compatible_paths_with t' p) args)

(* path equivalence *)

noeq type path_equiv (#vars:Type0) (#eqs:equations vars) : path vars -> path vars -> Type = 
  | Refl   : p:path vars
          -> path_equiv #vars #eqs p p
  | Sym    : p1:path vars -> p2:path vars
          -> path_equiv #vars #eqs p1 p2
          -> path_equiv #vars #eqs p2 p1
  | Trans  : p1:path vars -> p2:path vars -> p3:path vars
          -> path_equiv #vars #eqs p1 p2
          -> path_equiv #vars #eqs p2 p3
          -> path_equiv #vars #eqs p1 p3
  | Subst  : p:path vars -> p1:(vars -> path vars) -> p2:(vars -> path vars)
          -> (v:vars -> path_equiv #vars #eqs (p1 v) (p2 v))
          -> path_equiv #vars #eqs (path_subst p p1) (path_subst p p2)
  | Paths1 : e:equation vars{in_equations e eqs}
          -> p1:path vars{path_in_tree p1 (Eq?.left e)}
          -> p2:path vars{path_in_tree p2 (Eq?.right e)}
          -> _:unit{compatible_paths p1 p2}
          -> path_equiv #vars #eqs p1 p2
  | Paths2 : e:equation vars{in_equations e eqs}
          -> p:path vars{path_in_tree p (Eq?.left e) /\ Some? (path_ends_with p)}
          -> _:unit{~(has_compatible_paths_with (Eq?.right e) p)}
          -> path_equiv #vars #eqs p Bot
  | Paths3 : e:equation vars{in_equations e eqs}
          -> p:path vars{path_in_tree p (Eq?.right e) /\ Some? (path_ends_with p)}
          -> _:unit{~(has_compatible_paths_with (Eq?.left e) p)}
          -> path_equiv #vars #eqs p Bot
  (* ... *)

  (* but what if p ~ bot by one equation and p ~ p' by another equation? *)

