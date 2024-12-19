(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes 
*)

(* 
   There is a choice that this could  written with fewer wrappers by curring more,
   instead of the wrapI...O... pattern functions.
   There should be a way to get much more sharing with just a few combinators.
   id \o zin \o zout ... that sort of thing.
   But then you'll be debugging each all about twice as much.
   86 wrap calls, 49 reuses in those, not too bad this way.
   Probably just about as unreadable. 
   80 lines of ml, 86 lines of mli. 
   Plus the z in some of the wrappers certainly shortens the lines.
*)

open Unix
open Z
open FStar_Wrap_OCaml

(* 
   As Unix.t are the subtypes here:
   of_t maps Unix.t to t       - used on the outputs
   to_t maps t      to Unix.t  - used on the inputs
 *)

type error =
    E2BIG
  | EACCES
  | EAGAIN
  | EBADF
  | EBUSY
  | ECHILD
  | EDEADLK
  | EDOM
  | EEXIST
  | EFAULT
  | EFBIG
  | EINTR
  | EINVAL
  | EIO
  | EISDIR
  | EMFILE
  | EMLINK
  | ENAMETOOLONG
  | ENFILE
  | ENODEV
  | ENOENT
  | ENOEXEC
  | ENOLCK
  | ENOMEM
  | ENOSPC
  | ENOSYS
  | ENOTDIR
  | ENOTEMPTY
  | ENOTTY
  | ENXIO
  | EPERM
  | EPIPE
  | ERANGE
  | EROFS
  | ESPIPE
  | ESRCH
  | EXDEV
  | EWOULDBLOCK
  | EINPROGRESS
  | EALREADY
  | ENOTSOCK
  | EDESTADDRREQ
  | EMSGSIZE
  | EPROTOTYPE
  | ENOPROTOOPT
  | EPROTONOSUPPORT
  | ESOCKTNOSUPPORT
  | EOPNOTSUPP
  | EPFNOSUPPORT
  | EAFNOSUPPORT
  | EADDRINUSE
  | EADDRNOTAVAIL
  | ENETDOWN
  | ENETUNREACH
  | ENETRESET
  | ECONNABORTED
  | ECONNRESET
  | ENOBUFS
  | EISCONN
  | ENOTCONN
  | ESHUTDOWN
  | ETOOMANYREFS
  | ETIMEDOUT
  | ECONNREFUSED
  | EHOSTDOWN
  | EHOSTUNREACH
  | ELOOP
  | EOVERFLOW
  | EUNKNOWNERR of Z.t

let to_error (e: error) =
  match e with
  | E2BIG -> Unix.E2BIG
  | EACCES -> Unix.EACCES
  | EAGAIN -> Unix.EAGAIN
  | EBADF -> Unix.EBADF
  | EBUSY -> Unix.EBUSY
  | ECHILD -> Unix.ECHILD
  | EDEADLK -> Unix.EDEADLK
  | EDOM -> Unix.EDOM
  | EEXIST -> Unix.EEXIST
  | EFAULT -> Unix.EFAULT
  | EFBIG -> Unix.EFBIG
  | EINTR -> Unix.EINTR
  | EINVAL -> Unix.EINVAL
  | EIO -> Unix.EIO
  | EISDIR -> Unix.EISDIR
  | EMFILE -> Unix.EMFILE
  | EMLINK -> Unix.EMLINK
  | ENAMETOOLONG -> Unix.ENAMETOOLONG
  | ENFILE -> Unix.ENFILE
  | ENODEV -> Unix.ENODEV
  | ENOENT -> Unix.ENOENT
  | ENOEXEC -> Unix.ENOEXEC
  | ENOLCK -> Unix.ENOLCK
  | ENOMEM -> Unix.ENOMEM
  | ENOSPC -> Unix.ENOSPC
  | ENOSYS -> Unix.ENOSYS
  | ENOTDIR -> Unix.ENOTDIR
  | ENOTEMPTY -> Unix.ENOTEMPTY
  | ENOTTY -> Unix.ENOTTY
  | ENXIO -> Unix.ENXIO
  | EPERM -> Unix.EPERM
  | EPIPE -> Unix.EPIPE
  | ERANGE -> Unix.ERANGE
  | EROFS -> Unix.EROFS
  | ESPIPE -> Unix.ESPIPE
  | ESRCH -> Unix.ESRCH
  | EXDEV -> Unix.EXDEV
  | EWOULDBLOCK -> Unix.EWOULDBLOCK
  | EINPROGRESS -> Unix.EINPROGRESS
  | EALREADY -> Unix.EALREADY
  | ENOTSOCK -> Unix.ENOTSOCK
  | EDESTADDRREQ -> Unix.EDESTADDRREQ
  | EMSGSIZE -> Unix.EMSGSIZE
  | EPROTOTYPE -> Unix.EPROTOTYPE
  | ENOPROTOOPT -> Unix.ENOPROTOOPT
  | EPROTONOSUPPORT -> Unix.EPROTONOSUPPORT
  | ESOCKTNOSUPPORT -> Unix.ESOCKTNOSUPPORT
  | EOPNOTSUPP -> Unix.EOPNOTSUPP
  | EPFNOSUPPORT -> Unix.EPFNOSUPPORT
  | EAFNOSUPPORT -> Unix.EAFNOSUPPORT
  | EADDRINUSE -> Unix.EADDRINUSE
  | EADDRNOTAVAIL -> Unix.EADDRNOTAVAIL
  | ENETDOWN -> Unix.ENETDOWN
  | ENETUNREACH -> Unix.ENETUNREACH
  | ENETRESET -> Unix.ENETRESET
  | ECONNABORTED -> Unix.ECONNABORTED
  | ECONNRESET -> Unix.ECONNRESET
  | ENOBUFS -> Unix.ENOBUFS
  | EISCONN -> Unix.EISCONN
  | ENOTCONN -> Unix.ENOTCONN
  | ESHUTDOWN -> Unix.ESHUTDOWN
  | ETOOMANYREFS -> Unix.ETOOMANYREFS
  | ETIMEDOUT -> Unix.ETIMEDOUT
  | ECONNREFUSED -> Unix.ECONNREFUSED
  | EHOSTDOWN -> Unix.EHOSTDOWN
  | EHOSTUNREACH -> Unix.EHOSTUNREACH
  | ELOOP -> Unix.ELOOP
  | EOVERFLOW -> Unix.EOVERFLOW
  | EUNKNOWNERR i -> Unix.EUNKNOWNERR (Z.to_int i)

let of_error (e: Unix.error) =
  match e with
  | Unix.E2BIG -> E2BIG
  | Unix.EACCES -> EACCES
  | Unix.EAGAIN -> EAGAIN
  | Unix.EBADF -> EBADF
  | Unix.EBUSY -> EBUSY
  | Unix.ECHILD -> ECHILD
  | Unix.EDEADLK -> EDEADLK
  | Unix.EDOM -> EDOM
  | Unix.EEXIST -> EEXIST
  | Unix.EFAULT -> EFAULT
  | Unix.EFBIG -> EFBIG
  | Unix.EINTR -> EINTR
  | Unix.EINVAL -> EINVAL
  | Unix.EIO -> EIO
  | Unix.EISDIR -> EISDIR
  | Unix.EMFILE -> EMFILE
  | Unix.EMLINK -> EMLINK
  | Unix.ENAMETOOLONG -> ENAMETOOLONG
  | Unix.ENFILE -> ENFILE
  | Unix.ENODEV -> ENODEV
  | Unix.ENOENT -> ENOENT
  | Unix.ENOEXEC -> ENOEXEC
  | Unix.ENOLCK -> ENOLCK
  | Unix.ENOMEM -> ENOMEM
  | Unix.ENOSPC -> ENOSPC
  | Unix.ENOSYS -> ENOSYS
  | Unix.ENOTDIR -> ENOTDIR
  | Unix.ENOTEMPTY -> ENOTEMPTY
  | Unix.ENOTTY -> ENOTTY
  | Unix.ENXIO -> ENXIO
  | Unix.EPERM -> EPERM
  | Unix.EPIPE -> EPIPE
  | Unix.ERANGE -> ERANGE
  | Unix.EROFS -> EROFS
  | Unix.ESPIPE -> ESPIPE
  | Unix.ESRCH -> ESRCH
  | Unix.EXDEV -> EXDEV
  | Unix.EWOULDBLOCK -> EWOULDBLOCK
  | Unix.EINPROGRESS -> EINPROGRESS
  | Unix.EALREADY -> EALREADY
  | Unix.ENOTSOCK -> ENOTSOCK
  | Unix.EDESTADDRREQ -> EDESTADDRREQ
  | Unix.EMSGSIZE -> EMSGSIZE
  | Unix.EPROTOTYPE -> EPROTOTYPE
  | Unix.ENOPROTOOPT -> ENOPROTOOPT
  | Unix.EPROTONOSUPPORT -> EPROTONOSUPPORT
  | Unix.ESOCKTNOSUPPORT -> ESOCKTNOSUPPORT
  | Unix.EOPNOTSUPP -> EOPNOTSUPP
  | Unix.EPFNOSUPPORT -> EPFNOSUPPORT
  | Unix.EAFNOSUPPORT -> EAFNOSUPPORT
  | Unix.EADDRINUSE -> EADDRINUSE
  | Unix.EADDRNOTAVAIL -> EADDRNOTAVAIL
  | Unix.ENETDOWN -> ENETDOWN
  | Unix.ENETUNREACH -> ENETUNREACH
  | Unix.ENETRESET -> ENETRESET
  | Unix.ECONNABORTED -> ECONNABORTED
  | Unix.ECONNRESET -> ECONNRESET
  | Unix.ENOBUFS -> ENOBUFS
  | Unix.EISCONN -> EISCONN
  | Unix.ENOTCONN -> ENOTCONN
  | Unix.ESHUTDOWN -> ESHUTDOWN
  | Unix.ETOOMANYREFS -> ETOOMANYREFS
  | Unix.ETIMEDOUT -> ETIMEDOUT
  | Unix.ECONNREFUSED -> ECONNREFUSED
  | Unix.EHOSTDOWN -> EHOSTDOWN
  | Unix.EHOSTUNREACH -> EHOSTUNREACH
  | Unix.ELOOP -> ELOOP
  | Unix.EOVERFLOW -> EOVERFLOW
  | Unix.EUNKNOWNERR i -> EUNKNOWNERR (Z.of_int i)

exception Unix_error of error * string * string
let error_message : error -> string = wrapIwaOb error_message to_error
let handle_unix_error : ('a -> 'b) -> 'a -> 'b = handle_unix_error
let environment : unit -> string array  = environment
let unsafe_environment : unit -> string array  = unsafe_environment
let getenv : string -> string = getenv
let unsafe_getenv : string -> string = unsafe_getenv
let putenv : string -> string -> unit = putenv

type process_status =
    WEXITED of Z.t
  | WSIGNALED of Z.t
  | WSTOPPED of Z.t

let of_process_status (e: Unix.process_status) =
  match e with
  | Unix.WEXITED   i -> WEXITED   (Z.of_int i)
  | Unix.WSIGNALED i -> WSIGNALED (Z.of_int i)
  | Unix.WSTOPPED  i -> WSTOPPED  (Z.of_int i)

let to_process_status (e: process_status) =
  match e with
  | WEXITED   i -> Unix.WEXITED   (Z.to_int i)
  | WSIGNALED i -> Unix.WSIGNALED (Z.to_int i)
  | WSTOPPED  i -> Unix.WSTOPPED  (Z.to_int i)

type wait_flag = Unix.wait_flag = 
 WNOHANG | WUNTRACED

let to_wait_flag wf =
  match wf with
  | WNOHANG -> Unix.WNOHANG
  | WUNTRACED -> Unix.WUNTRACED

let execv : string -> string array -> 'a = execv
let execve : string -> string array -> string array -> 'a = execve
let execvp : string -> string array -> 'a = execvp
let execvpe : string -> string array -> string array -> 'a = execvpe

let fork : unit -> Z.t = wrapIaOz fork
let wait : unit -> Z.t * process_status = wrapIaOpzwb wait of_process_status
let waitpid : wait_flag list -> Z.t -> Z.t * process_status = 
    wrapILwazOpzwb waitpid to_wait_flag of_process_status

let system : string -> process_status = wrapIaOwb system of_process_status

let _exit : Z.t -> 'a     = wrapIzOa _exit
let getpid : unit -> Z.t  = wrapIaOz getpid
let getppid : unit -> Z.t = wrapIaOz getppid
let nice : Z.t -> Z.t     = wrapIzOz nice

type file_descr = Unix.file_descr

(* Why are these not from the channels? 
let stdout = Out_channel.stdout
let stderr = Out_channel.stderr
let stdin  = In_channel.stdin
 *)

let stdout = Unix.stdout
let stderr = Unix.stderr
let stdin  = Unix.stdin

type open_flag = Unix.open_flag = 
    O_RDONLY | O_WRONLY | O_RDWR | O_NONBLOCK | O_APPEND | O_CREAT | O_TRUNC 
  | O_EXCL | O_NOCTTY | O_DSYNC | O_SYNC | O_RSYNC   
  | O_SHARE_DELETE | O_CLOEXEC | O_KEEPEXEC
 
let to_open_flag f =
 match f with
  | O_RDONLY        -> Unix.O_RDONLY
  | O_WRONLY        -> Unix.O_WRONLY
  | O_RDWR          -> Unix.O_RDWR
  | O_NONBLOCK      -> Unix.O_NONBLOCK
  | O_APPEND        -> Unix.O_APPEND
  | O_CREAT         -> Unix.O_CREAT
  | O_TRUNC         -> Unix.O_TRUNC
  | O_EXCL          -> Unix.O_EXCL
  | O_NOCTTY        -> Unix.O_NOCTTY
  | O_DSYNC         -> Unix.O_DSYNC
  | O_SYNC          -> Unix.O_SYNC
  | O_RSYNC         -> Unix.O_RSYNC
  | O_SHARE_DELETE  -> Unix.O_SHARE_DELETE
  | O_CLOEXEC       -> Unix.O_CLOEXEC
  | O_KEEPEXEC      -> Unix.O_KEEPEXEC

let to_open_flag_list ofl = List.map to_open_flag ofl
   
type file_perm = Z.t
let openfile : string -> open_flag list -> file_perm -> file_descr = 
      wrapIabwcOd openfile Z.to_int 
let close : file_descr -> unit = close
let fsync : file_descr -> unit = fsync


let read : file_descr -> bytes -> Z.t -> Z.t -> Z.t = wrapIabzzOz read
let write : file_descr -> bytes -> Z.t -> Z.t -> Z.t = wrapIabzzOz write
let single_write : file_descr -> bytes -> Z.t -> Z.t -> Z.t = 
    wrapIabzzOz single_write
let write_substring : file_descr -> string -> Z.t -> Z.t -> Z.t = 
    wrapIabzzOz write_substring
let single_write_substring : file_descr -> string -> Z.t -> Z.t -> Z.t =
    wrapIabzzOz single_write_substring

let in_channel_of_descr : file_descr -> in_channel   = in_channel_of_descr
let out_channel_of_descr : file_descr -> out_channel = out_channel_of_descr
let descr_of_in_channel : in_channel -> file_descr   = descr_of_in_channel
let descr_of_out_channel : out_channel -> file_descr = descr_of_out_channel

type seek_command = Unix.seek_command = 
    SEEK_SET
  | SEEK_CUR
  | SEEK_END

let of_seek_command (sc : Unix.seek_command) = 
  match sc with
  | Unix.SEEK_SET -> SEEK_SET
  | Unix.SEEK_CUR -> SEEK_CUR
  | Unix.SEEK_END -> SEEK_END  

let lseek : file_descr -> Z.t -> seek_command -> Z.t = wrapIazwbOz lseek of_seek_command

let truncate : string -> Z.t -> unit      = wrapIazOb truncate
let ftruncate : file_descr -> Z.t -> unit = wrapIazOb ftruncate

type file_kind = Unix.file_kind = 
    S_REG | S_DIR | S_CHR | S_BLK | S_LNK | S_FIFO | S_SOCK

type stats = 
  { st_dev : Z.t;
    st_ino : Z.t;
    st_kind : file_kind;
    st_perm : Z.t;
    st_nlink : Z.t;
    st_uid : Z.t;
    st_gid : Z.t;
    st_rdev : Z.t;
    st_size : Z.t;
    st_atime : float;
    st_mtime : float;
    st_ctime : float;
  }

let of_stats (s : Unix.stats) =
  { st_dev   = Z.of_int s.st_dev;
    st_ino   = Z.of_int s.st_ino;
    st_kind  = s.st_kind;
    st_perm  = Z.of_int s.st_perm;
    st_nlink = Z.of_int s.st_nlink;
    st_uid   = Z.of_int s.st_uid;
    st_gid   = Z.of_int s.st_gid;
    st_rdev  = Z.of_int s.st_rdev;
    st_size  = Z.of_int s.st_size;
    st_atime = s.st_atime;
    st_mtime = s.st_mtime;
    st_ctime = s.st_ctime;
  }

let stat     : string -> stats          = wrapIaOwb stat  of_stats
let lstat    : string -> stats          = wrapIaOwb lstat of_stats
let fstat    : file_descr -> stats      = wrapIaOwb fstat of_stats
let isatty   : file_descr -> bool       = isatty
let unlink   : string -> unit           = unlink
let rename   : string -> string -> unit = rename
let link     : string -> string -> unit = link
let realpath : string -> string         = realpath

type access_permission = Unix.access_permission = 
  R_OK | W_OK | X_OK | F_OK

let chmod : string -> file_perm -> unit       = wrapIawbOc chmod Z.to_int 
let fchmod : file_descr -> file_perm -> unit  = wrapIawbOc fchmod Z.to_int
let chown : string -> Z.t -> Z.t -> unit      = wrapIazzOb chown
let fchown : file_descr -> Z.t -> Z.t -> unit = wrapIazzOb fchown
let umask : file_perm -> file_perm            = wrapIwaOwb  umask Z.to_int Z.of_int
let access : string -> access_permission list -> unit = access
let dup  : file_descr -> file_descr = dup
let dup2 : file_descr -> file_descr -> unit = dup2

let set_nonblock : file_descr -> unit        = set_nonblock
let clear_nonblock : file_descr -> unit      = clear_nonblock
let set_close_on_exec : file_descr -> unit   = set_close_on_exec
let clear_close_on_exec : file_descr -> unit = clear_close_on_exec
let mkdir : string -> file_perm -> unit      = wrapIawbOc mkdir Z.to_int
let rmdir : string -> unit = rmdir
let chdir : string -> unit = chdir
let getcwd : unit -> string = getcwd
let chroot : string -> unit = chroot

type dir_handle = Unix.dir_handle

let opendir : string -> dir_handle         = opendir
let readdir : dir_handle -> string         = readdir
let rewinddir : dir_handle -> unit         = rewinddir
let closedir : dir_handle -> unit          = closedir
let pipe : unit -> file_descr * file_descr = pipe
let mkfifo : string -> file_perm -> unit   = wrapIawbOc mkfifo Z.to_int

let create_process 
  : string -> string array -> file_descr -> file_descr -> file_descr -> Z.t = 
  wrapIabcdeOz create_process

let create_process_env : string -> string array -> string array -> file_descr ->  
    file_descr -> file_descr -> Z.t = wrapIabcdefOz create_process_env


let open_process_in : string -> in_channel = open_process_in
let open_process_out : string -> out_channel = open_process_out
let open_process : string -> in_channel * out_channel = open_process

let open_process_full : string -> string array -> in_channel * out_channel * in_channel =
  open_process_full

let open_process_args : string -> string array -> in_channel * out_channel = open_process_args
let open_process_args_in : string -> string array -> in_channel = open_process_args_in
let open_process_args_out : string -> string array -> out_channel = open_process_args_out
let open_process_args_full : string -> string array -> string array ->
    in_channel * out_channel * in_channel  = open_process_args_full
let process_in_pid : in_channel -> Z.t = wrapIaOz process_in_pid
let process_out_pid : out_channel -> Z.t = wrapIaOz process_out_pid
let process_pid : in_channel * out_channel -> Z.t = wrapIaOz process_pid
let process_full_pid : in_channel * out_channel * in_channel -> Z.t = 
  wrapIaOz process_full_pid

let close_process_in : in_channel -> process_status = 
  wrapIaOwb close_process_in of_process_status
let close_process_out : out_channel -> process_status = 
  wrapIaOwb close_process_out of_process_status

let close_process : in_channel * out_channel -> process_status = 
     wrapIaOwb close_process of_process_status

let close_process_full : in_channel * out_channel * in_channel -> process_status = 
    wrapIaOwb close_process_full of_process_status

let symlink     : string -> string -> unit = symlink
let has_symlink : unit -> bool             = has_symlink
let readlink    : string -> string         = readlink

let select : file_descr list -> file_descr list -> file_descr list ->
    float -> file_descr list * file_descr list * file_descr list = select

type lock_command = Unix.lock_command = 
  F_ULOCK | F_LOCK | F_TLOCK | F_TEST | F_RLOCK | F_TRLOCK

let lockf : file_descr -> lock_command -> Z.t -> unit = wrapIabzOc lockf
let kill : Z.t -> Z.t -> unit = wrapIzzOa kill

type sigprocmask_command = Unix.sigprocmask_command = 
    SIG_SETMASK
  | SIG_BLOCK
  | SIG_UNBLOCK

let to_sigprocmask_command spmc =
 match spmc with 
  | SIG_SETMASK -> Unix.SIG_SETMASK
  | SIG_BLOCK   -> Unix.SIG_BLOCK
  | SIG_UNBLOCK -> Unix.SIG_UNBLOCK


let sigprocmask : sigprocmask_command -> Z.t list -> Z.t list = 
    wrapIaLbOLwc sigprocmask Z.to_int Z.of_int 

let sigpending : unit -> Z.t list = wrapIaOLwb sigpending Z.of_int

let sigsuspend : Z.t list -> unit = wrapILwaOb sigsuspend Z.to_int 

let pause : unit -> unit = pause

(* Where is sigwait? 
let sigwait : Z.t list -> Z.t = wrapILwaOb sigwait Z.to_int
 *)

type process_times = Unix.process_times = 
  { tms_utime : float;
    tms_stime : float;
    tms_cutime : float;
    tms_cstime : float;
  }

let of_process_times (pt : Unix.process_times) : process_times = pt

type tm =
  { tm_sec   : Z.t;
    tm_min   : Z.t;
    tm_hour  : Z.t;
    tm_mday  : Z.t;
    tm_mon   : Z.t;
    tm_year  : Z.t;
    tm_wday  : Z.t;
    tm_yday  : Z.t;
    tm_isdst : bool;
  }

let to_tm (t : tm) : Unix.tm = 
  { tm_sec   = Z.to_int t.tm_sec;
    tm_min   = Z.to_int t.tm_min;
    tm_hour  = Z.to_int t.tm_hour;
    tm_mday  = Z.to_int t.tm_mday;
    tm_mon   = Z.to_int t.tm_mon;
    tm_year  = Z.to_int t.tm_year;
    tm_wday  = Z.to_int t.tm_wday;
    tm_yday  = Z.to_int t.tm_yday;
    tm_isdst = t.tm_isdst;
  }

let of_tm (t : Unix.tm) : tm = 
  { tm_sec   = Z.of_int t.tm_sec;
    tm_min   = Z.of_int t.tm_min;
    tm_hour  = Z.of_int t.tm_hour;
    tm_mday  = Z.of_int t.tm_mday;
    tm_mon   = Z.of_int t.tm_mon;
    tm_year  = Z.of_int t.tm_year;
    tm_wday  = Z.of_int t.tm_wday;
    tm_yday  = Z.of_int t.tm_yday;
    tm_isdst = t.tm_isdst;
  }

let time         : unit -> float                    = time
let gettimeofday : unit -> float                    = gettimeofday
let gmtime       : float -> tm                      = wrapIaOwb gmtime of_tm
let localtime    : float -> tm                      = wrapIaOwb localtime of_tm
let mktime       : tm -> float * tm                 = wrapIwaOpbwc mktime to_tm of_tm
let alarm        : Z.t -> Z.t                       = wrapIzOz alarm
let sleep        : Z.t -> unit                      = wrapIzOa sleep
let sleepf       : float -> unit                    = sleepf
let times        : unit -> process_times            = times
let utimes       : string -> float -> float -> unit = utimes

type interval_timer = Unix.interval_timer = 
 ITIMER_REAL | ITIMER_VIRTUAL | ITIMER_PROF 

type interval_timer_status = Unix.interval_timer_status = 
  { it_interval : float;
    it_value : float;
  }

let getitimer : interval_timer -> interval_timer_status = getitimer
let setitimer : interval_timer -> interval_timer_status -> interval_timer_status = setitimer
let getuid : unit -> Z.t  = wrapIaOz getuid
let geteuid : unit -> Z.t = wrapIaOz geteuid
let setuid : Z.t -> unit  = wrapIzOa setuid
let getgid : unit -> Z.t  = wrapIaOz getgid
let getegid : unit -> Z.t = wrapIaOz getegid
let setgid : Z.t -> unit  = wrapIzOa setgid
let getgroups : unit -> Z.t array = wrapIaOwA getgroups of_int 
let setgroups : Z.t array -> unit = wrapIAaOb setgroups to_int 

let initgroups : string -> Z.t -> unit = wrapIazOb initgroups

type passwd_entry =
  { pw_name : string;
    pw_passwd : string;
    pw_uid : Z.t;
    pw_gid : Z.t;
    pw_gecos : string;
    pw_dir : string;
    pw_shell : string
  }

let of_passwd_entry (pwe : Unix.passwd_entry) : passwd_entry =
  { pw_name   = pwe.pw_name;
    pw_passwd = pwe.pw_passwd;
    pw_uid    = Z.of_int pwe.pw_uid;
    pw_gid    = Z.of_int pwe.pw_gid;
    pw_gecos  = pwe.pw_gecos;
    pw_dir    = pwe.pw_dir;
    pw_shell  = pwe.pw_shell;
  }

type group_entry =
  { gr_name : string;
    gr_passwd : string;
    gr_gid : Z.t;
    gr_mem : string array
  }

let of_group_entry (ge : Unix.group_entry) : group_entry =
  { gr_name   = ge.gr_name;
    gr_passwd = ge.gr_passwd;
    gr_gid    = Z.of_int ge.gr_gid;
    gr_mem    = ge.gr_mem;
  }

let getlogin : unit -> string = getlogin
let getpwnam : string -> passwd_entry = wrapIaOwb  getpwnam of_passwd_entry
let getgrnam : string -> group_entry  = wrapIaOwb  getgrnam of_group_entry
let getpwuid : Z.t    -> passwd_entry = wrapIazOwb getpwuid of_passwd_entry
let getgrgid : Z.t    -> group_entry  = wrapIazOwb getgrgid of_group_entry

type inet_addr = Unix.inet_addr
let inet_addr_of_string : string -> inet_addr = inet_addr_of_string
let string_of_inet_addr : inet_addr -> string = string_of_inet_addr
let inet_addr_any       : inet_addr           = inet_addr_any
let inet_addr_loopback  : inet_addr           = inet_addr_loopback
let inet6_addr_any      : inet_addr           = inet6_addr_any
let inet6_addr_loopback : inet_addr           = inet6_addr_loopback
let is_inet6_addr       : inet_addr -> bool   = is_inet6_addr

type socket_domain = Unix.socket_domain =  
 PF_UNIX | PF_INET | PF_INET6

let of_socket_domain (sd: Unix.socket_domain) =
  match sd with
  | Unix.PF_UNIX  -> PF_UNIX
  | Unix.PF_INET  -> PF_INET
  | Unix.PF_INET6 -> PF_INET6

let to_socket_domain (sd: socket_domain) : Unix.socket_domain =
  match sd with
  | PF_UNIX  -> Unix.PF_UNIX
  | PF_INET  -> Unix.PF_INET
  | PF_INET6 -> Unix.PF_INET6

type socket_type = Unix.socket_type = 
 SOCK_STREAM | SOCK_DGRAM | SOCK_RAW  | SOCK_SEQPACKET 

let of_socket_type (st: Unix.socket_type) = 
  match st with
  | Unix.SOCK_STREAM    -> SOCK_STREAM
  | Unix.SOCK_DGRAM     -> SOCK_DGRAM
  | Unix.SOCK_RAW       -> SOCK_RAW
  | Unix.SOCK_SEQPACKET -> SOCK_SEQPACKET
  
let to_socket_type (st: socket_type) : Unix.socket_type = 
  match st with
  | SOCK_STREAM    -> Unix.SOCK_STREAM
  | SOCK_DGRAM     -> Unix.SOCK_DGRAM
  | SOCK_RAW       -> Unix.SOCK_RAW
  | SOCK_SEQPACKET -> Unix.SOCK_SEQPACKET

type sockaddr =
  ADDR_UNIX of string 
| ADDR_INET of inet_addr * Z.t

let of_sockaddr (sa : Unix.sockaddr) =
  match sa with
  | Unix.ADDR_UNIX s       -> ADDR_UNIX s
  | Unix.ADDR_INET (ia, i) -> ADDR_INET (ia, Z.of_int i)
    
let to_sockaddr (sa : sockaddr) =
  match sa with
  | ADDR_UNIX s       -> Unix.ADDR_UNIX s
  | ADDR_INET (ia, i) -> Unix.ADDR_INET (ia, Z.to_int i)


let socket : socket_domain -> socket_type -> Z.t -> file_descr = 
      wrapIwawbwcOd socket to_socket_domain to_socket_type Z.to_int 

let domain_of_sockaddr : sockaddr -> socket_domain = 
      wrapIwaOwb domain_of_sockaddr to_sockaddr of_socket_domain

let socketpair : socket_domain -> socket_type -> Z.t -> file_descr * file_descr = 
      wrapIwawbwcOd socketpair to_socket_domain to_socket_type Z.to_int 

let accept : file_descr -> file_descr * sockaddr = 
      wrapIaOpbwc accept of_sockaddr

let bind : file_descr -> sockaddr -> unit = wrapIawbOc bind to_sockaddr

let connect : file_descr -> sockaddr -> unit = wrapIawbOc connect to_sockaddr

let listen : file_descr -> Z.t -> unit = wrapIazOb listen

type shutdown_command = Unix.shutdown_command = 
    SHUTDOWN_RECEIVE | SHUTDOWN_SEND | SHUTDOWN_ALL

let shutdown : file_descr -> shutdown_command -> unit = shutdown
let getsockname : file_descr -> sockaddr = wrapIaOwb getsockname of_sockaddr
let getpeername : file_descr -> sockaddr = wrapIaOwb getpeername of_sockaddr

type msg_flag = Unix.msg_flag = 
    MSG_OOB | MSG_DONTROUTE | MSG_PEEK

let recv :  file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t = 
   wrapIabwcwdeOwf recv Z.to_int Z.to_int Z.of_int
let send :  file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t = 
   wrapIabwcwdeOwf send Z.to_int Z.to_int Z.of_int
let send_substring : file_descr -> string -> Z.t -> Z.t -> msg_flag list -> Z.t = 
   wrapIabwcwdeOwf send_substring Z.to_int Z.to_int Z.of_int

let sendto      
     : file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> sockaddr -> Z.t = 
     wrapIabwcwdewfOwg sendto           Z.to_int Z.to_int to_sockaddr Z.of_int 
let sendto_substring 
     : file_descr -> string -> Z.t -> Z.t -> msg_flag list  -> sockaddr -> Z.t = 
     wrapIabwcwdewfOwg sendto_substring Z.to_int Z.to_int to_sockaddr Z.of_int 

let recvfrom : file_descr -> bytes -> Z.t -> Z.t -> msg_flag list -> Z.t * sockaddr = 
     wrapIabwcwdeOwNSwfwg recvfrom Z.to_int Z.to_int Z.of_int of_sockaddr

type socket_bool_option = Unix.socket_bool_option = 
    SO_DEBUG | SO_BROADCAST | SO_REUSEADDR | SO_KEEPALIVE | SO_DONTROUTE
  | SO_OOBINLINE | SO_ACCEPTCONN | TCP_NODELAY | IPV6_ONLY | SO_REUSEPORT

type socket_int_option = Unix.socket_int_option = 
    SO_SNDBUF | SO_RCVBUF | SO_ERROR | SO_TYPE | SO_RCVLOWAT | SO_SNDLOWAT

type socket_optint_option = Unix.socket_optint_option = 
   SO_LINGER 
type socket_float_option = Unix.socket_float_option = 
   SO_RCVTIMEO | SO_SNDTIMEO

let getsockopt     : file_descr -> socket_bool_option -> bool         = getsockopt
let setsockopt     : file_descr -> socket_bool_option -> bool -> unit = setsockopt
let getsockopt_int : file_descr -> socket_int_option -> Z.t =
     wrapIabOwc getsockopt_int Z.of_int 
let setsockopt_int : file_descr -> socket_int_option -> Z.t -> unit = 
     wrapIabzOc setsockopt_int

let getsockopt_optint : file_descr -> socket_optint_option -> Z.t option = 
     wrapIabOwNSc getsockopt_optint Z.of_int

let setsockopt_optint : file_descr -> socket_optint_option -> Z.t option -> unit = 
     wrapIabwNScOd setsockopt_optint Z.to_int

let getsockopt_float : file_descr -> socket_float_option -> float = getsockopt_float
let setsockopt_float : file_descr -> socket_float_option -> float -> unit = setsockopt_float
let getsockopt_error : file_descr -> error option = wrapIaOwNSb getsockopt_error of_error

let open_connection     : sockaddr -> in_channel * out_channel = 
  wrapIwaOb open_connection to_sockaddr
let shutdown_connection : in_channel -> unit = shutdown_connection
let establish_server : (in_channel -> out_channel -> unit) -> sockaddr -> unit = 
    wrapIawbOc establish_server to_sockaddr

type host_entry = Unix.host_entry = 
  { h_name : string;
    h_aliases : string array;
    h_addrtype : socket_domain;
    h_addr_list : inet_addr array
  }

type protocol_entry = (* Unix.protocol_entry = *)
  { p_name : string;
    p_aliases : string array;
    p_proto : Z.t
  }

let of_protocol_entry (pe : Unix.protocol_entry) : protocol_entry =
  { p_name    = pe.p_name;
    p_aliases = pe.p_aliases;
    p_proto   = Z.of_int pe.p_proto;
  }

type service_entry =
  { s_name : string;
    s_aliases : string array;
    s_port : Z.t;
    s_proto : string
  }

let of_service_entry (se: Unix.service_entry) =
  { s_name = se.s_name;
    s_aliases = se.s_aliases;
    s_port = Z.of_int se.s_port;
    s_proto = se.s_proto;
  }

let gethostname      : unit -> string                    = wrapIaOb gethostname
let gethostbyname    : string -> host_entry              = gethostbyname
let gethostbyaddr    : inet_addr -> host_entry           = gethostbyaddr
let getprotobyname   : string -> protocol_entry          = 
   wrapIaOwb getprotobyname of_protocol_entry

let getprotobynumber : Z.t -> protocol_entry             = 
     wrapIwaOwb getprotobynumber Z.to_int of_protocol_entry
let getservbyname    : string -> string -> service_entry = 
      wrapIabOwc getservbyname of_service_entry
let getservbyport    : Z.t -> string -> service_entry    = 
      wrapIwabOwc getservbyport Z.to_int of_service_entry

type addr_info =
  { ai_family : socket_domain;
    ai_socktype : socket_type;
    ai_protocol : Z.t;
    ai_addr : sockaddr;
    ai_canonname : string
  }

let of_addr_info (ai : Unix.addr_info) =
  { ai_family    = ai.ai_family;
    ai_socktype  = ai.ai_socktype;
    ai_protocol  = Z.of_int ai.ai_protocol;
    ai_addr      = of_sockaddr ai.ai_addr;
    ai_canonname = ai.ai_canonname;
  }  

type getaddrinfo_option =
    AI_FAMILY of socket_domain
  | AI_SOCKTYPE of socket_type
  | AI_PROTOCOL of Z.t
  | AI_NUMERICHOST
  | AI_CANONNAME
  | AI_PASSIVE

let to_getaddrinfo_option (g : getaddrinfo_option) =
  match g with
  | AI_FAMILY sd   -> Unix.AI_FAMILY sd
  | AI_SOCKTYPE st -> Unix.AI_SOCKTYPE st
  | AI_PROTOCOL z  -> Unix.AI_PROTOCOL (Z.to_int z)
  | AI_NUMERICHOST -> Unix.AI_NUMERICHOST
  | AI_CANONNAME   -> Unix.AI_CANONNAME
  | AI_PASSIVE     -> Unix.AI_PASSIVE

let getaddrinfo: string -> string -> getaddrinfo_option list -> addr_info list = 
  wrapIabLwcOLwd getaddrinfo to_getaddrinfo_option of_addr_info

type name_info = Unix.name_info = 
  { ni_hostname : string;
    ni_service : string;
  }

type getnameinfo_option = Unix.getnameinfo_option = 
    NI_NOFQDN | NI_NUMERICHOST | NI_NAMEREQD | NI_NUMERICSERV | NI_DGRAM

let getnameinfo : sockaddr -> getnameinfo_option list -> name_info = 
       wrapIwabOc getnameinfo to_sockaddr

type terminal_io = 
  {
     c_ignbrk : bool;
     c_brkint : bool;
     c_ignpar : bool;
     c_parmrk : bool;
     c_inpck : bool;
     c_istrip : bool;
     c_inlcr : bool;
     c_igncr : bool;
     c_icrnl : bool;
     c_ixon : bool;
     c_ixoff : bool;

     c_opost : bool;

     c_obaud : Z.t;
     c_ibaud : Z.t;
     c_csize  : Z.t;
     c_cstopb : Z.t;
     c_cread : bool;
     c_parenb : bool;
     c_parodd : bool;
     c_hupcl : bool;
     c_clocal : bool;

     c_isig : bool;
     c_icanon : bool;
     c_noflsh : bool;
     c_echo : bool;
     c_echoe : bool;
     c_echok : bool;
     c_echonl : bool;

     c_vintr : int;
     c_vquit : int;
     c_verase : int;
     c_vkill : int;
     c_veof : int;
     c_veol : int;
     c_vmin : int;
     c_vtime : int;
     c_vstart : int;
     c_vstop : int;
  }


let of_terminal_io (tio : Unix.terminal_io) : terminal_io =
    {
     c_ignbrk = tio.c_ignbrk;
     c_brkint = tio.c_brkint;
     c_ignpar = tio.c_ignpar;
     c_parmrk = tio.c_parmrk;
     c_inpck = tio.c_inpck;
     c_istrip = tio.c_istrip;
     c_inlcr = tio.c_inlcr;
     c_igncr = tio.c_igncr;
     c_icrnl = tio.c_icrnl;
     c_ixon = tio.c_ixon;
     c_ixoff = tio.c_ixoff;

     c_opost = tio.c_opost;

     c_obaud = Z.of_int tio.c_obaud;
     c_ibaud = Z.of_int tio.c_ibaud;
     c_csize = Z.of_int tio.c_csize;
     c_cstopb = Z.of_int tio.c_cstopb;
     c_cread = tio.c_cread;
     c_parenb = tio.c_parenb;
     c_parodd = tio.c_parodd;
     c_hupcl = tio.c_hupcl;
     c_clocal = tio.c_clocal;

     c_isig = tio.c_isig;
     c_icanon = tio.c_icanon;
     c_noflsh = tio.c_noflsh;
     c_echo = tio.c_echo;
     c_echoe = tio.c_echoe;
     c_echok = tio.c_echok;
     c_echonl = tio.c_echonl;

     c_vintr = Char.code tio.c_vintr;
     c_vquit = Char.code tio.c_vquit;
     c_verase = Char.code tio.c_verase;
     c_vkill = Char.code tio.c_vkill;
     c_veof = Char.code tio.c_veof;
     c_veol = Char.code tio.c_veol;
     c_vmin =  tio.c_vmin;
     c_vtime = tio.c_vtime;
     c_vstart = Char.code tio.c_vstart;
     c_vstop = Char.code  tio.c_vstop;
  }

let to_terminal_io (tio : terminal_io) : Unix.terminal_io =
    {
     c_ignbrk = tio.c_ignbrk;
     c_brkint = tio.c_brkint;
     c_ignpar = tio.c_ignpar;
     c_parmrk = tio.c_parmrk;
     c_inpck = tio.c_inpck;
     c_istrip = tio.c_istrip;
     c_inlcr = tio.c_inlcr;
     c_igncr = tio.c_igncr;
     c_icrnl = tio.c_icrnl;
     c_ixon = tio.c_ixon;
     c_ixoff = tio.c_ixoff;

     c_opost = tio.c_opost;

     c_obaud = Z.to_int tio.c_obaud;
     c_ibaud = Z.to_int tio.c_ibaud;
     c_csize = Z.to_int tio.c_csize;
     c_cstopb = Z.to_int tio.c_cstopb;
     c_cread = tio.c_cread;
     c_parenb = tio.c_parenb;
     c_parodd = tio.c_parodd;
     c_hupcl = tio.c_hupcl;
     c_clocal = tio.c_clocal;

     c_isig = tio.c_isig;
     c_icanon = tio.c_icanon;
     c_noflsh = tio.c_noflsh;
     c_echo = tio.c_echo;
     c_echoe = tio.c_echoe;
     c_echok = tio.c_echok;
     c_echonl = tio.c_echonl;

     c_vintr = Char.chr tio.c_vintr;
     c_vquit = Char.chr tio.c_vquit;
     c_verase = Char.chr tio.c_verase;
     c_vkill = Char.chr  tio.c_vkill;
     c_veof  = Char.chr  tio.c_veof;
     c_veol  = Char.chr tio.c_veol;
     c_vmin   = tio.c_vmin;
     c_vtime  = tio.c_vtime;
     c_vstart = Char.chr tio.c_vstart;
     c_vstop  = Char.chr  tio.c_vstop;
  }

let tcgetattr : file_descr -> terminal_io = 
      wrapIaOwb tcgetattr of_terminal_io

type setattr_when = Unix.setattr_when = 
    TCSANOW | TCSADRAIN | TCSAFLUSH

let tcsetattr : file_descr -> setattr_when -> terminal_io -> unit = 
    wrapIabwcOd tcsetattr to_terminal_io

let tcsendbreak : file_descr -> Z.t -> unit = wrapIazOb tcsendbreak
let tcdrain : file_descr -> unit            = tcdrain

type flush_queue = Unix.flush_queue = 
    TCIFLUSH | TCOFLUSH | TCIOFLUSH

let tcflush : file_descr -> flush_queue -> unit = tcflush 

type flow_action = Unix.flow_action = 
    TCOOFF | TCOON | TCIOFF | TCION

let tcflow : file_descr -> flow_action -> unit = tcflow
let setsid : unit -> Z.t = wrapIaOz setsid
