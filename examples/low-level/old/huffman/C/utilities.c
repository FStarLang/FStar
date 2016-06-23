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

#include <stdlib.h>
#include <string.h>
#include "huffman.h"

/* Temporary variables for use in writing/reading files. See epic.h. */
Byte temp_byte;   
short temp_short;
int temp_int;

char *check_malloc (int size)
{
  char *the_block;

  the_block = malloc(size);
  if (the_block == NULL)
      {
      printf("\nERROR: unable to allocate sufficient memory!\n");
      exit(-1);
      }
  return(the_block);
  }

void check_free (char *ptr)
{
  if (ptr != NULL)
    free (ptr);
  }

FILE *check_fopen (char *filename, char *read_write_flag)
{
  FILE *fp;
  
  fp = fopen(filename, read_write_flag);
  if (fp == NULL) 
      { 
      printf("\nError opening file %s (%s).\n", filename, read_write_flag); 
      exit(-1);
      }
  return(fp);
  }

char *concatenate(char *string1, char *string2)
{
  char *new_string = check_malloc ( strlen(string1) + strlen(string2) + 1 );

  strcpy (new_string, string1);
  strcat (new_string, string2);
  return (new_string);
  }
