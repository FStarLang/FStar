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

(* Wrapper of OCaml unix.mli minimized code, see the OCaml library for docs. *)

module FStar.Unix
open FStar.Char
open FStar.Bytes
open FStar.Float
open FStar.All 

module IA = FStar.ImmutableArray
module IAB = FStar.ImmutableArray.Base

module IC = FStar.In_Channel
type in_channel  = IC.t

module OC = FStar.Out_Channel
type out_channel = OC.t

type error =
  | E2BIG
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
  | EUNKNOWNERR of int

exception Unix_error of error * string * string
val error_message : error -> ML string
val handle_unix_error : ('a -> 'b) -> 'a -> ML 'b
val environment : unit -> ML (IAB.t string)
val unsafe_environment : unit -> ML (IAB.t string)
val getenv : string -> ML string
val unsafe_getenv : string -> ML string
val putenv : string -> string -> ML unit
type process_status =
  | WEXITED of int
  | WSIGNALED of int
  | WSTOPPED of int

type wait_flag =
  | WNOHANG
  | WUNTRACED
val execv : string -> IAB.t string -> ML 'a
val execve : string -> IAB.t string -> IAB.t string -> ML 'a
val execvp : string -> IAB.t string -> ML 'a
val execvpe : string -> IAB.t string -> IAB.t string -> ML 'a
val fork : unit -> ML int
val wait : unit -> ML (int * process_status)
val waitpid : list wait_flag -> int -> ML (int * process_status)
val system : string -> ML process_status
val _exit : int -> ML 'a
val getpid : unit -> ML int
val getppid : unit -> ML int
val nice : int -> ML int
assume new type file_descr
val stdin : file_descr
val stdout : file_descr
val stderr : file_descr
type open_flag =
  | O_RDONLY
  | O_WRONLY
  | O_RDWR
  | O_NONBLOCK
  | O_APPEND
  | O_CREAT
  | O_TRUNC
  | O_EXCL
  | O_NOCTTY
  | O_DSYNC
  | O_SYNC
  | O_RSYNC
  | O_SHARE_DELETE
  | O_CLOEXEC
  | O_KEEPEXEC

type file_perm = int
val openfile : string -> list open_flag -> file_perm -> ML file_descr
val close : file_descr -> ML unit
val fsync : file_descr -> ML unit
val read : file_descr -> bytes -> int -> int -> ML int
val write : file_descr -> bytes -> int -> int -> ML int
val single_write : file_descr -> bytes -> int -> int -> ML int
val write_substring : file_descr -> string -> int -> int -> ML int
val single_write_substring :
  file_descr -> string -> int -> int -> ML int
val in_channel_of_descr : file_descr -> ML in_channel
val out_channel_of_descr : file_descr -> ML out_channel
val descr_of_in_channel : in_channel -> ML file_descr
val descr_of_out_channel : out_channel -> ML file_descr
type seek_command = | SEEK_SET | SEEK_CUR  | SEEK_END
val lseek : file_descr -> int -> seek_command -> ML int
val truncate : string -> int -> ML unit
val ftruncate : file_descr -> int -> ML unit
type file_kind = | S_REG  | S_DIR  | S_CHR  | S_BLK | S_LNK  | S_FIFO
                 | S_SOCK
noeq type stats =
  { st_dev : int;
    st_ino : int;
    st_kind : file_kind;
    st_perm : file_perm;
    st_nlink : int;
    st_uid : int;
    st_gid : int;
    st_rdev : int;
    st_size : int;
    st_atime : float;
    st_mtime : float;
    st_ctime : float;
  }

val stat : string -> ML stats
val lstat : string -> ML stats
val fstat : file_descr -> ML stats
val isatty : file_descr -> ML bool
val unlink : string -> ML unit
val rename : string -> string -> ML unit
val link : string -> string -> ML unit
val realpath : string -> ML string
type access_permission = | R_OK  | W_OK  | X_OK | F_OK
val chmod : string -> file_perm -> ML unit
val fchmod : file_descr -> file_perm -> ML unit
val chown : string -> int -> int -> ML unit
val fchown : file_descr -> int -> int -> ML unit
val umask : file_perm -> ML file_perm
val access : string -> list access_permission -> ML unit
val dup : file_descr -> ML file_descr
val dup2 : file_descr -> file_descr -> ML unit
val set_nonblock : file_descr -> ML unit
val clear_nonblock : file_descr -> ML unit
val set_close_on_exec : file_descr -> ML unit
val clear_close_on_exec : file_descr -> ML unit
val mkdir : string -> file_perm -> ML unit
val rmdir : string -> ML unit
val chdir : string -> ML unit
val getcwd : unit -> ML string
val chroot : string -> ML unit

assume new type dir_handle
val opendir : string -> ML dir_handle
val readdir : dir_handle -> ML string
val rewinddir : dir_handle -> ML unit
val closedir : dir_handle -> ML unit
val pipe : unit -> ML (file_descr * file_descr)
val mkfifo : string -> file_perm -> ML unit
val create_process : string -> IAB.t string -> file_descr -> file_descr -> file_descr -> ML int
val create_process_env :
  string -> IAB.t string -> IAB.t string -> file_descr ->
    file_descr -> file_descr -> ML int
val open_process_in : string -> ML in_channel
val open_process_out : string -> ML out_channel
val open_process : string -> ML (in_channel * out_channel)
val open_process_full :
  string -> IAB.t string -> ML (in_channel * out_channel * in_channel)
val open_process_args : string -> IAB.t string -> ML (in_channel * out_channel)
val open_process_args_in : string -> IAB.t string -> ML in_channel
val open_process_args_out : string -> IAB.t string -> ML out_channel
val open_process_args_full :
  string -> IAB.t string -> IAB.t string -> ML (in_channel * out_channel * in_channel)
val process_in_pid : in_channel -> ML int
val process_out_pid : out_channel -> ML int
val process_pid : in_channel * out_channel -> ML int
val process_full_pid : in_channel * out_channel * in_channel -> ML int
val close_process_in : in_channel -> ML process_status
val close_process_out : out_channel -> ML process_status
val close_process : in_channel * out_channel -> ML process_status
val close_process_full :
  in_channel * out_channel * in_channel -> ML process_status
val symlink : string -> string -> ML unit
val has_symlink : unit -> ML bool
val readlink : string -> ML string
val select : list file_descr -> list file_descr -> list file_descr ->
    float -> ML (list file_descr * list file_descr * list file_descr)
type lock_command = | F_ULOCK | F_LOCK | F_TLOCK | F_TEST
  | F_RLOCK  | F_TRLOCK
val lockf : file_descr -> lock_command -> int -> ML unit
val kill : int -> int -> ML unit

type sigprocmask_command = |  SIG_SETMASK | SIG_BLOCK | SIG_UNBLOCK
val sigprocmask : sigprocmask_command -> list int -> ML (list int)
val sigpending : unit -> ML (list int)
val sigsuspend : list int -> ML unit
val pause : unit -> ML unit
val sigwait : list int -> ML int

noeq type process_times =
  { tms_utime : float;
    tms_stime : float;
    tms_cutime : float;
    tms_cstime : float;
  }

type tm =
  { tm_sec : int;
    tm_min : int;
    tm_hour : int;
    tm_mday : int;
    tm_mon : int;
    tm_year : int;
    tm_wday : int;
    tm_yday : int;
    tm_isdst : bool;
  }
val time : unit -> ML float
val gettimeofday : unit -> ML float
val gmtime : float -> ML tm
val localtime : float -> ML tm
val mktime : tm -> ML (float * tm)
val alarm : int -> ML int
val sleep : int -> ML unit
val sleepf : float -> ML unit
val times : unit -> ML process_times
val utimes : string -> float -> float -> ML unit

type interval_timer = | ITIMER_REAL | ITIMER_VIRTUAL | ITIMER_PROF

noeq type interval_timer_status =
  { it_interval : float;
    it_value : float;
  }
val getitimer : interval_timer -> ML interval_timer_status
val setitimer : interval_timer -> interval_timer_status -> ML interval_timer_status
val getuid : unit -> ML int
val geteuid : unit -> ML int
val setuid : int -> ML unit
val getgid : unit -> ML int
val getegid : unit -> ML int
val setgid : int -> ML unit
val getgroups : unit -> ML (IAB.t int)
val setgroups : IAB.t int -> ML unit
val initgroups : string -> int -> ML unit

type passwd_entry =
  { pw_name : string;
    pw_passwd : string;
    pw_uid : int;
    pw_gid : int;
    pw_gecos : string;
    pw_dir : string;
    pw_shell : string
  }

noeq type group_entry =
  { gr_name : string;
    gr_passwd : string;
    gr_gid : int;
    gr_mem : IAB.t string
  }
val getlogin : unit -> ML string
val getpwnam : string -> ML passwd_entry
val getgrnam : string -> ML group_entry
val getpwuid : int -> ML passwd_entry
val getgrgid : int -> ML group_entry

assume new type inet_addr
val inet_addr_of_string : string -> ML inet_addr
val string_of_inet_addr : inet_addr -> ML string
val inet_addr_any : inet_addr
val inet_addr_loopback : inet_addr
val inet6_addr_any : inet_addr
val inet6_addr_loopback : inet_addr
val is_inet6_addr : inet_addr -> ML bool

type socket_domain = | PF_UNIX | PF_INET | PF_INET6

type socket_type = | SOCK_STREAM | SOCK_DGRAM | SOCK_RAW | SOCK_SEQPACKET

noeq type sockaddr = | ADDR_UNIX of string | ADDR_INET of inet_addr * int
val socket : bool -> socket_domain -> socket_type -> int -> ML file_descr
val domain_of_sockaddr: sockaddr -> ML socket_domain
val socketpair : socket_domain -> socket_type -> int -> ML (file_descr * file_descr)
val accept : file_descr -> ML (file_descr * sockaddr)
val bind : file_descr -> sockaddr -> ML unit
val connect : file_descr -> sockaddr -> ML unit
val listen : file_descr -> int -> ML unit

type shutdown_command = | SHUTDOWN_RECEIVE | SHUTDOWN_SEND | SHUTDOWN_ALL
val shutdown : file_descr -> shutdown_command -> ML unit
val getsockname : file_descr -> ML sockaddr
val getpeername : file_descr -> ML sockaddr
type msg_flag = | MSG_OOB | MSG_DONTROUTE | MSG_PEEK
val recv :  file_descr -> bytes -> int -> int -> list msg_flag -> ML int
val recvfrom : file_descr -> bytes -> int -> int -> list msg_flag -> ML (int * sockaddr)
val send : file_descr -> bytes -> int -> int -> list msg_flag -> ML int
val send_substring : file_descr -> string -> int -> int -> list msg_flag -> ML int
val sendto : file_descr -> bytes -> int -> int -> list msg_flag -> sockaddr -> ML int
val sendto_substring : file_descr -> string -> int -> int -> list msg_flag  -> sockaddr -> ML int

type socket_bool_option = | SO_DEBUG | SO_BROADCAST | SO_REUSEADDR | SO_KEEPALIVE
  | SO_DONTROUTE | SO_OOBINLINE | SO_ACCEPTCONN | TCP_NODELAY  | IPV6_ONLY
  | SO_REUSEPORT

type socket_int_option = | SO_SNDBUF | SO_RCVBUF | SO_ERROR | SO_TYPE
  | SO_RCVLOWAT  | SO_SNDLOWAT

type socket_optint_option = | SO_LINGER
type socket_float_option = | SO_RCVTIMEO | SO_SNDTIMEO
val getsockopt : file_descr -> socket_bool_option -> ML bool
val setsockopt : file_descr -> socket_bool_option -> bool -> ML unit
val getsockopt_int : file_descr -> socket_int_option -> ML int
val setsockopt_int : file_descr -> socket_int_option -> int -> ML unit
val getsockopt_optint : file_descr -> socket_optint_option -> ML (option int)
val setsockopt_optint : file_descr -> socket_optint_option -> option int -> ML unit
val getsockopt_float : file_descr -> socket_float_option -> ML float
val setsockopt_float : file_descr -> socket_float_option -> float -> ML unit
val getsockopt_error : file_descr -> ML (option error)
val open_connection : sockaddr -> ML (in_channel * out_channel)
val shutdown_connection : in_channel -> ML unit
val establish_server :  (in_channel -> out_channel -> unit) -> sockaddr -> ML unit

noeq type host_entry =
  { h_name : string;
    h_aliases : IAB.t string;
    h_addrtype : socket_domain;
    h_addr_list : IAB.t inet_addr
  }

noeq type protocol_entry =
  { p_name : string;
    p_aliases : IAB.t string;
    p_proto : int
  }

noeq type service_entry =
  { s_name : string;
    s_aliases : IAB.t string;
    s_port : int;
    s_proto : string
  }
val gethostname : unit -> ML string
val gethostbyname : string -> ML host_entry
val gethostbyaddr : inet_addr -> ML host_entry
val getprotobyname : string -> ML protocol_entry
val getprotobynumber : int -> ML protocol_entry
val getservbyname : string -> string -> ML service_entry
val getservbyport : int -> string -> ML service_entry

noeq type addr_info =
  { ai_family : socket_domain;
    ai_socktype : socket_type;
    ai_protocol : int;
    ai_addr : sockaddr;
    ai_canonname : string
  }

type getaddrinfo_option =
  | AI_FAMILY of socket_domain
  | AI_SOCKTYPE of socket_type
  | AI_PROTOCOL of int
  | AI_NUMERICHOST
  | AI_CANONNAME
  | AI_PASSIVE

val getaddrinfo: string -> string -> list getaddrinfo_option -> ML (list addr_info)

type name_info =
  { ni_hostname : string;
    ni_service : string;
  }

type getnameinfo_option = | NI_NOFQDN | NI_NUMERICHOST | NI_NAMEREQD | NI_NUMERICSERV
  | NI_DGRAM
val getnameinfo : sockaddr -> list getnameinfo_option -> ML name_info
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
    c_obaud : int;
    c_ibaud : int;
    c_csize : int;
    c_cstopb : int;
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
val tcgetattr : file_descr -> ML terminal_io
type setattr_when = | TCSANOW | TCSADRAIN  | TCSAFLUSH
val tcsetattr : file_descr -> setattr_when -> terminal_io -> ML unit
val tcsendbreak : file_descr -> int -> ML unit
val tcdrain : file_descr -> ML unit

type flush_queue = | TCIFLUSH | TCOFLUSH | TCIOFLUSH
val tcflush : file_descr -> flush_queue -> ML unit
type flow_action = | TCOOFF | TCOON | TCIOFF  | TCION
val tcflow : file_descr -> flow_action -> ML unit
val setsid : unit -> ML int
