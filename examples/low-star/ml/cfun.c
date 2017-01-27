#include <stdlib.h>
#include <stdio.h>
#include <sys/uio.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>

// the iovec struct is defined in sys/uio.h
typedef struct iovec buffer;

// This function takes : int -> bytes -> int as argument
CAMLprim value
ocaml_writev(value f, value buffers, value nb_buffers)
{
  CAMLparam3( f, buffers, nb_buffers);
  buffer *iov;
  int i, n, filedes, iovcnt;

  filedes = Int_val(f);
  iovcnt = Int_val(nb_buffers);
  iov = (buffer *)malloc(sizeof(buffer) * iovcnt);

  for (i = 0; i < iovcnt; i++) {
    iov[i].iov_base = String_val(Field(Field(buffers, i), 0))
                      + Int_val(Field(Field(buffers, i), 1));
    iov[i].iov_len = Int_val(Field(Field(buffers, i), 2));
  }

  n = (int)writev(filedes, iov, iovcnt);
  free(iov);
  return Val_int(n);
}

// TODO : test
CAMLprim value
ocaml_readv(value f, value buffers, value nb_buffers)
{
  CAMLparam3( f, buffers, nb_buffers);
  buffer *iov;
  int i, n, filedes, iovcnt;
  iovcnt = Int_val(nb_buffers);
  iov = (buffer *)malloc(sizeof(buffer) * iovcnt);

  filedes = Int_val(f);

  for (i = 0; i < iovcnt; i++) {
    iov[i].iov_base = String_val(Field(Field(buffers, i), 0))
                      + Int_val(Field(Field(buffers, i), 1));
    iov[i].iov_len = Int_val(Field(Field(buffers, i), 2));
  }

  n = (int)readv(filedes, iov, iovcnt);
  free(iov);
  return Val_int(n);
}
