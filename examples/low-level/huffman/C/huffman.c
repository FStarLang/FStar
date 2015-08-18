/*
--------------------------------------------------------------------- 
---		 EPIC (Efficient Pyramid Image Coder)             ---
---	 Designed by Eero P. Simoncelli and Edward H. Adelson     ---
---		    Written by Eero P. Simoncelli                 ---
---  Developed at the Vision Science Group, The Media Laboratory  ---
---	Copyright 1989, Massachusetts Institute of Technology     ---
---			 All rights reserved.                     ---
---------------------------------------------------------------------

Permission to use, copy, or modify this software and its documentation
for educational and research purposes only and without fee is hereby
granted, provided that this copyright notice appear on all copies and
supporting documentation.  For any other uses of this software, in
original or modified form, including but not limited to distribution
in whole or in part, specific prior permission must be obtained from
M.I.T. and the authors.  These programs shall not be used, rewritten,
or adapted as the basis of a commercial software or hardware product
without first obtaining appropriate licenses from M.I.T.  M.I.T. makes
no representations about the suitability of this software for any
purpose.  It is provided "as is" without express or implied warranty.

---------------------------------------------------------------------
*/

#include <math.h>
#include <string.h>
#include <stdlib.h>
#include "huffman.h"

/* 
=========================== DATA STRUCTURES ==============================
Nodes in the huffman tree. This is a little inefficient with memory,
since the nodes don't need the code slot, and the leaves don't need the
children slots.  A more efficient method would be to have a tag byte
indicating whether a struct was a node or leaf... 
==========================================================================
*/

struct node
  {
  unsigned int frequency;
  struct node *next;                    /* used to create an ordered list */
  struct node *zero_child, *one_child;
  SymbolType symbol;
  char *code;                           /* a string of 0's and 1's */
  };

/*
==========================================================================
huffman_encode() --
We build a histogram as an array of pointers to nodes.  We then build a 
huffman tree of these nodes.  We use the array to do quick encoding (array 
lookup).  The tree is used to create the codes, and later in decoding.  It is
stored in a packed form by reading it off in a depth-first fashion:  a stream 
of 0's is used to indicate successively deeper nodes in the tree, followed by a 1 
indicating a leaf, and the symbol associated with that leaf.  For now, we 
use a byte for each of the 0's and 1's, but eventually, we can pack them as
bits (in which case the symbols will have to be written across byte boundaries).
Returns the number of bytes in the encoded stream.
==========================================================================
*/


void compute_histogram (register SymbolType *symbol_stream, register int symbol_stream_length, register struct node **histogram);
void build_huffman_tree (register struct node **histogram, struct node **tree_ptr);
int encode_stream (SymbolType *symbol_stream, int symbol_stream_length, struct node **histogram, CodeType *encoded_stream);
int pack_huffman_tree (struct node *tree, Byte **packed_tree);
void free_tree_nodes (struct node *tree);
void insert_in_ordered_list (register struct node *the_node, register struct node **list);
void compute_code_strings (register struct node *tree, register char *code_string, register int code_string_pos);
int count_leaves (struct node *tree);
void pack_tree_iter (struct node *tree, Byte **packed_tree_ptr);

int huffman_encode (SymbolType *symbol_stream, int symbol_stream_length, Byte **packed_huffman_tree, int *huffman_tree_size, CodeType *encoded_stream)
                            
                           
                                         /* to be malloced */
                         
                                         /* already malloced */
  {
  struct node *histogram[NUM_SYMBOL_VALUES];
  struct node *huffman_tree;
  int encoded_stream_length;
  register int i;
  
  /* initialize histogram */
  for (i=0; i<NUM_SYMBOL_VALUES; i++)  histogram[i] = (struct node *) NULL;
  
  compute_histogram(symbol_stream, symbol_stream_length, histogram);
  build_huffman_tree(histogram, &huffman_tree);
  encoded_stream_length = 
    encode_stream(symbol_stream, symbol_stream_length, histogram, encoded_stream);
  *huffman_tree_size = pack_huffman_tree(huffman_tree, packed_huffman_tree);
  free_tree_nodes(huffman_tree);
  return (encoded_stream_length);
  }
  
void compute_histogram(register SymbolType *symbol_stream, register int symbol_stream_length, register struct node **histogram)
{
  register int i;
  register struct node *the_leaf;
  
  for (i=0; i<symbol_stream_length; i++, symbol_stream++)
      {
      the_leaf = histogram[ *symbol_stream ];  /* index into histogram from symbol */
      if (the_leaf == NULL)
	  {
	  the_leaf = histogram[ *symbol_stream ] =
	    (struct node *) check_malloc(sizeof(struct node));
	  the_leaf->symbol = *symbol_stream;
	  the_leaf->frequency = 1;
	  the_leaf->zero_child = the_leaf->one_child = NULL;
	  }
      else
	  (the_leaf->frequency)++;
      }
  }
  
void build_huffman_tree(register struct node **histogram, struct node **tree_ptr)
{
  struct node *tree = NULL;     /* cannot be a register since we need to pass its address */
  register struct node *new_node;
  char temp_code[ NUM_SYMBOL_VALUES ];     /* temporary string to store codes */
  register int i;

  /* Make an ordered list of nodes, sorted by frequency */
  for (i=0; i< NUM_SYMBOL_VALUES; i++)
    if (histogram[i] != NULL)
	insert_in_ordered_list(histogram[i], &tree);

  /*   print_list_nodes(tree,1); */

  /* Build the tree by recursively combining the first two (lowest freq) nodes */
  while (tree->next != NULL)
      {
      new_node = (struct node *) check_malloc(sizeof(struct node));
      new_node->zero_child = tree;
      new_node->one_child = tree->next;
      new_node->frequency = (new_node->zero_child->frequency + 
			     new_node->one_child->frequency);
      tree = tree->next->next;              /* throw away first two nodes */
      insert_in_ordered_list(new_node, &tree);
      }

  compute_code_strings(tree, temp_code, 0);
  *tree_ptr = tree;
  }
  
void insert_in_ordered_list(register struct node *the_node, register struct node **list)
{
  register struct node *the_list;
  
  the_list = *list;
  
  if ( (the_list == NULL) || (the_node->frequency <= the_list->frequency) )
      {
      the_node->next = the_list;
      (*list) = the_node;
      }
  else  
      {
      while ( (the_list->next != NULL) &&
	      (the_node->frequency > the_list->next->frequency) )
	the_list = (the_list->next);
      the_node->next = the_list->next;
      the_list->next = the_node;
      }
  }
  
/* recursively computes and stores the codes in each leaf of the tree */
void compute_code_strings(register struct node *tree, register char *code_string, register int code_string_pos)
{
  
  if ( tree->zero_child == NULL )    /* If leaf */
      {
      code_string[code_string_pos] = '\0';    /* terminate string */
      tree->code = strcpy(check_malloc(code_string_pos+1), code_string);
      }
  else
      {
      code_string[code_string_pos] = '0';
      compute_code_strings(tree->zero_child, code_string, code_string_pos+1);
      code_string[code_string_pos] = '1';
      compute_code_strings(tree->one_child, code_string, code_string_pos+1);
      }
  }

struct code_node *read_huffman_tree(FILE *file)
{
  register struct code_node *the_node;
  Byte the_byte;
  SymbolType the_symbol, exp;
  int i;

  the_node = (struct code_node *) check_malloc(sizeof(struct code_node));

  read_byte (the_byte, file);
  /* printf("%d ", the_byte); */
  if ( the_byte == 0 )
      {
      the_node->zero_child = read_huffman_tree(file);
      the_node->one_child = read_huffman_tree(file);
      }
  else if ( the_byte == 1 )
      {
      the_node->zero_child = the_node->one_child = NULL;
      the_symbol = 0;
      for (i=0, exp=1; i<sizeof(SymbolType); i++, exp<<=8)
	  {
	  read_byte(the_byte, file);
	  the_symbol += (the_byte * exp);
	  }
      the_node->symbol = the_symbol;
      /* printf("%04x ", the_symbol); */
      }
  else
      { printf("Error reading Huffman Tree!\n"); exit(-1); }
  return (the_node);
  }

void read_and_huffman_decode(FILE *file, struct code_node *tree, SymbolType *symbol_stream, int count)
{
  CodeType the_byte;
  register CodeType bit_mask = 0; 
  register struct code_node *the_node;
  register int i;

  for (i=0; i<count; i++)
      {
      the_node = tree;
      while (the_node->zero_child != NULL)
	  {
	  if (bit_mask == 0) { read_byte(the_byte, file); bit_mask = 1; }
	  if (bit_mask & the_byte)
	    the_node = the_node->one_child;
	  else the_node = the_node->zero_child;
	  bit_mask <<= 1;
	  }
      symbol_stream[i] = the_node->symbol;
      }
  }

/* NOTE: For machine independence, we do not assume anything about the number of
bits in CodeType */
int encode_stream(SymbolType *symbol_stream, int symbol_stream_length, struct node **histogram, CodeType *encoded_stream)
                            
                           
                           
                                 /* already malloced */
  {
  int i;
  struct node *the_node;
  register char *the_code_string;
  register CodeType *code_pointer = encoded_stream;
  register CodeType bit_mask = 1;
    
  *code_pointer = 0;
  for (i=0; i<symbol_stream_length; i++, symbol_stream++)
      {
      the_node = histogram[ *symbol_stream ];
      if (the_node == NULL) 
	  { printf("Error in histogram.  Unable to encode.\n"); exit(-1); }
      the_code_string = the_node->code;
      while (*the_code_string)
	  {
	  if (*the_code_string == '1')  *code_pointer |= bit_mask;
	  the_code_string++;
	  bit_mask <<= 1;
	  if (bit_mask == 0) { bit_mask = 1; code_pointer++; *code_pointer = 0; }
	  }
      }
  return (code_pointer-encoded_stream+1);
  }
  
/* Compute a byte block containing an encoded representation of the huffman tree. */
int pack_huffman_tree(struct node *tree, Byte **packed_tree)
{
  Byte *packed_tree_ptr;
  int num_leaves;

  num_leaves = count_leaves(tree);
  /* there are always num_leaves - 1 nodes in the tree */
  packed_tree_ptr = *packed_tree = 
    (Byte *) check_malloc(2*num_leaves+sizeof(SymbolType)*num_leaves-1);
  pack_tree_iter(tree, &packed_tree_ptr);
  return (packed_tree_ptr - *packed_tree);  /* return size of packed tree */
  }

/*
Recursively pack the tree in depth-first order.  Store a zero for each node, 
and a one followed by the corresponding symbol for each leaf. The symbols
are stored in a fixed (machine-independent) byte order.  (NOTE: this could
be rewritten to use htons and ntohs -- see <netinet/in.h> and <sys/types.h>
-- except that we then have to fix the symbol type!).
*/

void pack_tree_iter(struct node *tree, Byte **packed_tree_ptr)
{
  SymbolType the_symbol;
  int i;
  
  if ( tree->zero_child == NULL )
      {
      **packed_tree_ptr = 1;      /* leaf tag */
      (*packed_tree_ptr)++;
      the_symbol = tree->symbol;
      for (i=0; i<sizeof(SymbolType); i++)  /* for each byte of the symbol */
	  {
	  **packed_tree_ptr = the_symbol & 0xFF;
	  (*packed_tree_ptr)++;
	  the_symbol >>= 8;
	  }
      }
  else
      {
      **packed_tree_ptr = 0;      /* node tag */
      (*packed_tree_ptr)++;
      pack_tree_iter(tree->zero_child, packed_tree_ptr);
      pack_tree_iter(tree->one_child, packed_tree_ptr);
      }
  }

int count_leaves (struct node *tree)
{
  if (tree->zero_child == NULL) return(1);  /* if leaf, return 1 */
  else  return( count_leaves(tree->zero_child) + count_leaves(tree->one_child) );
  }

void free_tree_nodes(struct node *tree)
{
  if (tree->zero_child != NULL)
      {
      free_tree_nodes(tree->zero_child);
      free_tree_nodes(tree->one_child);
      }
  else check_free ((char *) tree->code);
  check_free ((char *) tree);
  }
  
void print_list_nodes(struct node *tree, int flag)
{
  if (flag) printf("Symbol Histogram: \n");
  printf("%04x: %d  ",tree->symbol, tree->frequency);
  if (tree->next != NULL)
    print_list_nodes(tree->next,0);
  else
    printf("\n");
  }
  
int main(int argc, char *argv[])
  {
  int i, length, encoded_stream_length;
  SymbolType *symbol_stream;
  Byte *packed_tree;
  struct code_node *the_tree;
  int tree_size;
  CodeType *encoded_stream;
  Byte bit_mask = 1;
  FILE *fp;

  length = argc-1;
  symbol_stream = (SymbolType *) check_malloc (length*sizeof(SymbolType));
  for (i=0; i<length; i++) symbol_stream[i] = atoi(argv[i+1]);
  encoded_stream = (CodeType *) check_malloc (length*sizeof(SymbolType));
  encoded_stream_length = 
  huffman_encode(symbol_stream, length, &packed_tree, &tree_size, encoded_stream);
  printf("Huffman coded to %d bytes.\n", encoded_stream_length);

  printf("Code: ");
  for (i=0; i<encoded_stream_length; i++)
    for (bit_mask=1; bit_mask; bit_mask<<=1)
      printf("%d ", ( ((encoded_stream[i])&bit_mask) ? 1 : 0));
  printf("\nTree (%d): ",tree_size);
  for (i=0; i<tree_size; i++)
      {
      if ( !(packed_tree[i]) )
	printf("%d ", packed_tree[i]);
      else
	  {
	  printf("%d:%02x%02x  ", packed_tree[i], packed_tree[i+1], packed_tree[i+2]);
	  i+=2;
	  }
      }

  fp = check_fopen ("test_data", "w");
  write_array(packed_tree, tree_size, fp);
  write_array(encoded_stream, encoded_stream_length, fp);
  fclose(fp);

  printf("\nReading file ...\n");
  fp = check_fopen ("test_data", "r");
  the_tree = read_huffman_tree(fp);
  read_and_huffman_decode(fp, the_tree, symbol_stream, length);
  
  printf("\nDecoded Symbol stream: ");
  for (i=0; i<length; i++)
  printf("%d ", symbol_stream[i]);
  printf("\n");
  return 0;
  }

/*
cc -o huffman +x huffman.c utilities.c
huffman  0 0 1 0 2 0 0 0 3 0 0 0 0 0 0 0 1 0 0 2 0 0 1 0 0 0 0 3 
*/
