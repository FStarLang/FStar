open Prims
type fd_string = Prims.string Prims.list
type fd_string_read = fd_string
type fd_string_write = fd_string
let (open_read_file : unit -> fd_string_read) =
  fun uu___ -> (fun uu___ -> Obj.magic []) uu___
let (open_write_file : unit -> fd_string_write) =
  fun uu___ -> (fun uu___ -> Obj.magic []) uu___
let (print_newline : fd_string_write -> fd_string_write) =
  fun uu___ -> (fun fdsw -> Obj.magic ("\n" :: (Obj.magic fdsw))) uu___
let (print_string : fd_string_write -> Prims.string -> fd_string_write) =
  fun uu___1 ->
    fun uu___ ->
      (fun fdsw -> fun s -> Obj.magic (s :: (Obj.magic fdsw))) uu___1 uu___
let (input_line : fd_string_read -> (Prims.string * fd_string_read)) =
  fun fdsr ->
    match Obj.magic fdsr with
    | [] -> FStar_Exn.raise FStar_IO.EOF
    | h::t -> (h, (Obj.magic t))
let (read_line : fd_string_read -> (Prims.string * fd_string_read)) =
  fun fdsr ->
    match Obj.magic fdsr with
    | [] -> FStar_Exn.raise FStar_IO.EOF
    | h::t -> (h, (Obj.magic t))
let (write_string : fd_string_write -> Prims.string -> fd_string_write) =
  fun uu___1 ->
    fun uu___ ->
      (fun fdsw -> fun s -> Obj.magic (s :: (Obj.magic fdsw))) uu___1 uu___
let (fd_write_to_fd_read : fd_string_write -> fd_string_read) =
  fun uu___ ->
    (fun fdsw -> Obj.magic (FStar_List_Tot_Base.rev (Obj.magic fdsw))) uu___
let (fd_write_to_string : fd_string_write -> Prims.string) =
  fun fdsw ->
    let fdsr = fd_write_to_fd_read fdsw in
    FStar_List_Tot_Base.fold_right (fun s1 -> fun s2 -> Prims.strcat s1 s2)
      (FStar_List_Tot_Base.rev (Obj.magic fdsw)) ""