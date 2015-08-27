(*
  This type corresponds to the iovec C structure :
  strut iovec{
    void *iov_base;
    size_t iov_len;
  };
*)
type buffer = { content: char array;
                start_idx:int;
                length:int}
