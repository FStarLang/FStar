#include <stdlib.h>
#include <stdbool.h>

/* instantiate with int */

struct ccell_lvalue;

typedef struct ccell_lvalue {
  int ccell_data;
  struct ccell_lvalue * ccell_next;
} * ccell_ptrvalue;

ccell_ptrvalue alloc_cell (int const data, ccell_ptrvalue const next) {
  ccell_ptrvalue res = malloc(sizeof(struct ccell_lvalue));
  res->ccell_data = data;
  res->ccell_next = next;
  return res;
}

struct cllist_lvalue;

typedef struct cllist_lvalue {
  ccell_ptrvalue cllist_head;
  ccell_ptrvalue * cllist_tail;
} * cllist_ptrvalue;

cllist_ptrvalue alloc_llist () {
  cllist_ptrvalue res = malloc(sizeof(struct cllist_lvalue));
  res->cllist_head = NULL;
  res->cllist_tail = &(res->cllist_head);
  return res;
}

bool is_empty(cllist_ptrvalue l) {
  return l->cllist_head == NULL;
}

int dequeue(cllist_ptrvalue l) {
  ccell_ptrvalue c = l->cllist_head;
  ccell_ptrvalue next = c->ccell_next;
  l->cllist_head = next;
  if (next == NULL)
    l->cllist_tail = &(l->cllist_head);
  return c->ccell_data;
}

void enqueue(cllist_ptrvalue l, int v) {
  ccell_ptrvalue c = alloc_cell(v, NULL);
  *(l->cllist_tail) = c;
  l->cllist_tail = &(c->ccell_next);
}
