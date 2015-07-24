#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include "stack.h"

/***********************************************************************/
/* Allocating OCaml values on the stack */
/***********************************************************************/

#define check(_p) if (!(_p)) { fprintf(stderr,"Failed check %s:%d\n",__FILE__,__LINE__); fflush(stdout); exit(1); }
#define Assert check

//#include <caml/gc.h> /* The below is copied from this file */
#define Caml_black (3 << 8)
/* This depends on the layout of the header.  See [mlvalues.h]. */
#define Make_header(wosize, tag, color)                                       \
      (/*Assert ((wosize) <= Max_wosize),*/                                   \
       ((header_t) (((header_t) (wosize) << 10)                               \
                    + (color)                                                 \
                    + (tag_t) (tag)))                                         \
      )

value stack_caml_alloc(mlsize_t wosize, tag_t tag, int nbits, int *mask) {
  value tmp, result;
  mlsize_t i;
  Assert (tag < 256);
  Assert (tag != Infix_tag);
  Assert (wosize != 0);
  tmp = (value)stack_alloc_maskp(Bhsize_wosize(wosize),nbits,mask);
  Assert (tmp != 0);
  Hd_hp (tmp) = Make_header (wosize, tag, Caml_black);
  result = Val_hp (tmp);
  if (tag < No_scan_tag){
    for (i = 0; i < wosize; i++) Field (result, i) = Val_unit;
  }
  return result;
}

value stack_caml_alloc_string (mlsize_t lenb)
{
  value result;
  mlsize_t offset_index;
  mlsize_t wosize = (lenb + sizeof (value)) / sizeof (value);
  result = stack_caml_alloc (wosize, String_tag, 0, NULL);
  Field (result, wosize - 1) = 0;
  offset_index = Bsize_wsize (wosize) - 1;
  Byte (result, offset_index) = offset_index - lenb;
  return result;
}

value stack_caml_alloc_tuple (mlsize_t n, int nbits, int *mask)
{
  return stack_caml_alloc(n, 0, nbits, mask);
}

/***********************************************************************/
/* GC scanning */
/***********************************************************************/

#if 0
/** TAKEN FROM OLEG'S DELIMCC STUFF */
/*
   Custom root-scanning function, to scan the captured delimited
   continuation, the body of the custom data type ekfragment.
   The function delimcc_scan_roots_ekfragments should be installed 
   as a GC's root-scanning hook. The function is a simple
   iterator that invokes delimcc_scan_roots_ekfragment
   on each ekfragment_struct in the list.

   The function delimcc_scan_roots_ekfragment is a minor adjustment
   of the function `caml_do_local_roots' in asmrun/roots.c.
   The adjustment is needed to install a scanning termination
   criterion. The function caml_do_local_roots assumes that
   there is a C-stack frame with the NULL Callback_link underneath
   the very first ML stack frame. Encountering that C-stack frame
   terminates the scan. Since we have captured only the part of
   ML stack, we do not have the dedicated C-stack frame to terminate
   the stack. We need a different criterion to end the scanning
   action.
 */

static void stack_scan_roots_page(scanning_action action,
					  const  ekp)
{
  char * sp       = (char*)(ekp->stack_fragment);
  uintnat retaddr = ekp->last_retaddr;

  const frame_descr * d;
  uintnat h;
#ifdef Stack_grows_upwards
  const short * p;  /* PR#4339: stack offsets are negative in this case */
#else
  const unsigned short * p;
#endif

#if defined(DEBUG) && DEBUG
  fprintf(stderr, 
	  "\ndelimcc_scan_roots_ekfragment for retaddr %lx\n",
	  retaddr);
#endif

  while (sp != NULL) {
    #if defined(DEBUG) && DEBUG
    fprintf(stderr, "sp       %p\n",sp);
    fprintf(stderr, "retaddr  %lx\n",retaddr);
    #endif
    /* Find the descriptor corresponding to the return address */
    h = Hash_retaddr(retaddr);
    while(1) {
      d = caml_frame_descriptors[h];
      if (d == NULL) 
	fprintf(stderr, 
		"Failed to find the descriptor for retaddr %lx; sp is %p\n",
		retaddr,sp), exit(8);
      if (d->retaddr == retaddr) break;
      h = (h+1) & caml_frame_descriptors_mask;
    }
    if (d->frame_size != 0xFFFF) {
      /* Scan the roots in this frame */
      int n;
      for (p = d->live_ofs, n = d->num_live; n > 0; n--, p++) {
	const int ofs = *p;
	value * root;
	if (ofs & 1) {
	  fprintf(stderr, 
		  "ekfragment scan: found live register %d, retaddr %lx\n",
		  ofs >> 1,retaddr), exit(8);
	  /*             root = regs + (ofs >> 1); */
	} else {
	  root = (value *)(sp + ofs);
	}
	action (*root, root);
      }
      /* Move to next frame */
#ifndef Stack_grows_upwards
      sp += (d->frame_size & 0xFFFC);
#else
      sp -= (d->frame_size & 0xFFFC);
#endif

      /* Custom termination: scanned the whole stack fragment */
      if (sp == ekp->top_of_stack)
	break;

      retaddr = RetAddr_from_frame(sp);
    } else {
      /* This marks the top of a stack chunk for an ML callback.
	 Skip C portion of stack and continue with next ML stack chunk.
	 We must report an error. Otherwise, we should have adjusted the
	 Callback_link pointers when we captured the fragment!
      */
      fprintf(stderr, "Found a C stack frame in the captured fragment!"
	      "retaddr %lx, sp (copied) %p\n",retaddr,sp);
      /*
        struct caml_context * next_context = Callback_link(sp);
        sp = next_context->bottom_of_stack;
        retaddr = next_context->last_retaddr;
        regs = next_context->gc_regs;
      */
      /* A null sp means no more ML stack chunks; stop here. */
    }
  }
}

static void delimcc_scan_roots_ekfragments(scanning_action action)
{
  ekfragment_t ekp = NULL;

  for(ekp = ekfragments; ekp != NULL; ekp = ekp->next)
    delimcc_scan_roots_ekfragment(action,ekp);

  /* Run the previous hook if any */
  if (prev_scan_roots_hook != NULL) (*prev_scan_roots_hook)(action);
}

#endif

/***********************************************************************/
/* FFI */
/***********************************************************************/

CAMLprim value stack_push_frame(value v) 
{
  int szb = Val_int(v);
  push_frame(szb);
  return Val_unit;
}

CAMLprim value stack_pop_frame() 
{
  pop_frame();
  return Val_unit;
}

CAMLprim value stack_mkpair(value v1, value v2) 
{
  CAMLparam2 (v1, v2);
  int mask[2];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 0;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 0;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(2,nbits,mask);
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  CAMLreturn(tuple);
}

CAMLprim value stack_mktuple3(value v1, value v2, value v3) {
  CAMLparam3 (v1, v2, v3);
  int mask[3];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 0;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 0;
    nbits++;
  }
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 0;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(3,nbits,mask);
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  Field(tuple, 2) = v3;
  CAMLreturn(tuple);
}

CAMLprim value stack_mktuple4(value v1, value v2, value v3, value v4) {
  CAMLparam4 (v1, v2, v3, v4);
  int mask[4];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 0;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 0;
    nbits++;
  }
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 0;
    nbits++;
  }
  if (!(Is_long(v4) || is_stack_pointer((void *)v4))) {
    mask[nbits] = 0;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(4,nbits,mask);
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  Field(tuple, 2) = v3;
  Field(tuple, 3) = v4;
  CAMLreturn(tuple);
}

CAMLprim value stack_mkemptystring(value vallen) {
  CAMLparam1 (vallen);
  int len = Int_val(vallen);
  CAMLreturn(stack_caml_alloc_string(len));
}

/***********************************************************************/
/* Tests */
/***********************************************************************/

static char *s = "This is a string!";
CAMLprim value make_string(value unit)
{
  int len;
  value res;

  len = strlen(s);
  res = stack_caml_alloc_string(len);
  memmove(String_val(res), s, len);
  return res;
}

void printptrs(void *ign, void **ptr) {
  printf("  live pointer addr=%p, val=%p\n",ptr,*ptr);
}

CAMLprim void print_mask(value unit) 
{
  CAMLparam1 (unit);
  printf("identifying marked pointers\n");
  each_marked_pointer(printptrs,0);
  CAMLreturn0;
}

CAMLprim void inspect(value v) 
{
  CAMLparam1 (v);
  if (Is_long(v)) {
    printf("is long %d (%ld)\n", Int_val(v), Long_val(v));
  } else {
    printf("is block: Wosize=%lu, Tag=%hhu\n", Wosize_val(v), Tag_val(v));
  }
  CAMLreturn0;
}
