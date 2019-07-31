module IOBase

open FStar.List

(** SECTION: Effect **)
 
type file_descriptor = int

noeq
type unix a = 
  | OpenFile : string -> (file_descriptor -> unix a) -> unix a
  | ReadFd   : file_descriptor -> (Bytes.bytes -> unix a) -> unix a
  | WriteFd  : file_descriptor -> Bytes.bytes -> unix a -> unix a
  | CloseFd  : file_descriptor -> unix a -> unix a
  | Return   : a -> unix a

type unix_event =
  | EOpenFile : file_name:string -> fd:file_descriptor -> unix_event
  | EReadFd   : fd:file_descriptor -> msg:Bytes.bytes -> unix_event
  | EWriteFd  : fd:file_descriptor -> msg:Bytes.bytes -> unix_event
  | ECloseFd  : fd:file_descriptor -> unix_event

type events_trace = list unix_event

let unix_post a = a -> events_trace -> Type0  // local_events (from old to new)
let unix_wpty a = events_trace -> unix_post a -> Type0  // past_events (from new to old; reversed compared with local_events)

let unix_return (a:Type) (x:a) = Return x

let rec unix_bind (a:Type) (b:Type) (l : unix a) (k : a -> unix b) : unix b =
  match l with
  | OpenFile file_name fnc -> OpenFile file_name (fun i -> 
                                                    FStar.WellFounded.axiom1 fnc i;
                                                    unix_bind _ _ (fnc i) k)
  | ReadFd fd fnc -> ReadFd fd (fun i ->
                                  FStar.WellFounded.axiom1 fnc i;
                                  unix_bind _ _ (fnc i) k)
  | WriteFd fd msg k' -> WriteFd fd msg (unix_bind _ _ k' k)
  | CloseFd fd k' -> CloseFd fd (unix_bind _ _ k' k)
  | Return v -> k v

unfold
let unix_return_wp (a:Type) (x:a) : unix_wpty a =
  fun past_events p -> p x []

unfold
let unix_bind_wp (_ : range) (a:Type) (b:Type) (w : unix_wpty a) (kw : a -> unix_wpty b) : unix_wpty b =
  fun past_events p -> 
    w past_events 
      (fun result local_events -> 
        kw result
           ((List.rev local_events) @ past_events) 
           (fun result' local_events' -> 
              p result' (local_events @ local_events')))
  
let rec unix_interpretation #a
  (m : unix a) 
  (past_events : events_trace)
  (p : unix_post a) : Type0 = 
  match m with
  | OpenFile file_name fnc -> 
             forall (fd : file_descriptor). 
                (FStar.WellFounded.axiom1 fnc fd;
                let event = (EOpenFile file_name fd) in
                unix_interpretation 
                    (fnc fd) 
                    (event::past_events) 
                    (fun x local_events -> p x (event::local_events)))
  
  | ReadFd fd fnc ->
           forall (msg : Bytes.bytes).
             (FStar.WellFounded.axiom1 fnc msg;
             let event = (EReadFd fd msg) in
             unix_interpretation
               (fnc msg)
               (event::past_events)
               (fun x local_events -> p x (event:: local_events)))

  | WriteFd fd msg m' ->
            let event = (EWriteFd fd msg) in
            unix_interpretation
              m' 
              (event::past_events) 
              (fun x local_events -> p x (event :: local_events))

  | CloseFd fd m' ->
            let event = (ECloseFd fd) in
            unix_interpretation
              m' 
              (event::past_events) 
              (fun x local_events -> p x (event :: local_events))

  | Return x -> p x []


total
reifiable
reflectable
new_effect {
  UNIX : a:Type -> Effect
  with 
       repr       = unix
     ; return     = unix_return
     ; bind       = unix_bind

     ; wp_type    = unix_wpty
     ; return_wp  = unix_return_wp
     ; bind_wp    = unix_bind_wp

     ; interp     = unix_interpretation
}

unfold let lift_PURE_UNIX (a:Type) (wp:pure_wp a) : unix_wpty a =
  fun past_events p ->
    wp (fun a -> p a [])
    
sub_effect PURE~> UNIX = lift_PURE_UNIX

effect Unix (a:Type) 
  (pre:(past_events:events_trace -> Type0)) 
  (post:(past_events:events_trace{pre past_events} -> a -> 
                   local_events:events_trace -> Type0)) =
    UNIX a (fun past_events p -> 
              pre past_events /\ 
                (forall result local_events.
                  post past_events result local_events ==> p result local_events))
(** SECTION: Actions **)
let rec is_open (fd:file_descriptor) (past_events: events_trace) :
  Tot Type0 =
  match past_events with
  | [] -> False
  | h :: tail -> match h with
               | EOpenFile _ fd' -> if fd = fd' then True
                                   else is_open fd tail
               | ECloseFd fd' -> if fd = fd' then False
                                  else is_open fd tail
               | _ -> is_open fd tail

let open_file (file_name:string) : 
  Unix file_descriptor 
    (requires (fun _ -> True))
    (ensures (fun past_events fd local_events -> 
      local_events = [EOpenFile file_name fd] /\ is_open fd ((List.rev local_events) @ past_events))) =
  Unix?.reflect (OpenFile file_name (fun fd -> Return fd))
       
let read (fd:file_descriptor) :
  Unix Bytes.bytes
    (requires (fun past_events -> is_open fd past_events))
    (ensures (fun _ msg local_events -> local_events = [EReadFd fd msg])) =
  Unix?.reflect (ReadFd fd (fun msg -> Return msg))

let write (fd:file_descriptor) (msg:Bytes.bytes) :
  Unix unit 
    (requires (fun past_events -> is_open fd past_events))
    (ensures (fun _ _ local_events -> local_events = [EWriteFd fd msg])) =
  Unix?.reflect (WriteFd fd msg (Return ()))

let close (fd:file_descriptor) :
  Unix unit
    (requires (fun past_events -> is_open fd past_events))
    (ensures (fun _ _ local_events -> local_events = [ECloseFd fd])) =
  Unix?.reflect (CloseFd fd (Return ()))


(** SECTION: Test static checking that policy is respected **)
let read_file (file_name:string) : 
//  UNIX Bytes.bytes (fun past_events p -> forall msg fd. p msg [EOpenFile file_name fd; EReadFd fd msg; ECloseFd fd])
  Unix Bytes.bytes
    (requires (fun _ -> True))
    (ensures (fun _ msg local_events ->
      exists fd.
        local_events = [EOpenFile file_name fd; 
                        EReadFd fd msg; 
                        ECloseFd fd]))
  =
                        
  let fd = open_file file_name in
  let msg = read fd in
  close fd; msg

let write_file (file_name:string) (msg:Bytes.bytes) :
  //UNIX unit (fun past_events p -> forall fd. p () [EOpenFile file_name fd; EWriteFd fd msg; ECloseFd fd])
  Unix unit 
    (requires (fun _ -> True))
    (ensures (fun _ _ local_events ->
      exists fd.
        local_events = [EOpenFile file_name fd; 
                        EWriteFd fd msg; 
                        ECloseFd fd]))
  =
  let fd = open_file file_name in
  write fd msg; close fd

(** [canWrite] is a function specifying whether a file [f] can be written *)
let canWrite (f:string) =
  match f with
  | "demo/tempfile" -> true
  | _ -> false

(** [canRead] is a function specifying whether a file [f] can be read *)
let canRead (f:string) =
  match f with
  | "demo/tempfile" -> true
  | "demo/README"   -> true
  | _ -> false

let rec remove_fd (fds : list (file_descriptor * string)) (fd : file_descriptor) :
  Tot (list (file_descriptor * string)) =
  match fds with
  | [] -> []
  | (fd', file_name) :: tail -> if fd' = fd then tail
                                else (fd', file_name) :: (remove_fd tail fd)
                        
let rec lookup_file_name (fds : list (file_descriptor * string)) (fd : file_descriptor) :
  Tot string =
  match fds with
  | [] -> "" // this should not be the case
  | (fd', file_name) :: tail -> if fd' = fd then file_name
                          else lookup_file_name tail fd

//[@(strict_on_arguments [1])]
let rec check_events (events:events_trace) : Tot ((fds : list (file_descriptor * string)) -> Type0) (decreases events) =
  fun fds ->
  match events with
  | [] -> True
  | event::tail -> 
      match event with
      | EOpenFile name fd -> check_events tail ((fd, name) :: fds)
      | ECloseFd fd -> check_events tail (remove_fd fds fd)
      | EReadFd fd _ -> let file_name = lookup_file_name fds fd in
                        canRead file_name /\ check_events tail fds
      | EWriteFd fd _ -> let file_name = lookup_file_name fds fd in
                         canWrite file_name /\ check_events tail fds
      | _ -> check_events tail fds 

// TODO: avoid fuel
#push-options "--initial_fuel 0 --max_fuel 0 --z3seed 0"

open FStar.Tactics

let test (x : unit) =
  assert True by (ignore (unify (quote x) (`())))

//#set-options "--debug IOBase --ugly"

let staticChecking () : 
  Unix unit 
    (requires (fun _ -> True))
    (ensures (fun _ _ local_events -> check_events local_events []))
      by (explode (); dump "ORIG";
          let b = match List.Tot.nth (cur_binders ()) 3 with
          | None -> fail "won't happen" | Some b -> b
          in
          let b' = instantiate (binder_to_term b) (`()) in
          let b'' = instantiate (binder_to_term b') (fresh_uvar None) in
          dump "before mapply";
          mapply (binder_to_term b'');
          dump "before compute";
          compute ();
          dump "before skolem";
          let _ = skolem () in
          dump "RW1";
          rewrite_eqs_from_context ();
          dump "RW2";
          compute ();
          trivial (); qed ())
      =

  let v1 = read_file "demo/tempfile" in
  let v2 = read_file "demo/README" in
  //let v3 = read_file "demo/password" in // invalid read, fails type-checking *)
  write_file "demo/tempfile" v1
  //write_file "demo/password" v1 // invalid write , fails type-checking
