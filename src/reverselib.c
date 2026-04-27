#include <stdlib.h>
#include <stdio.h>

struct ll {
  int x;
  struct ll* next;
};

void print_ll(void* addr)
{
  struct ll* node = addr;

  printf ("\n");
  while (node != NULL) {
    printf ("%p |-> (%d,%p)\n", node, node->x, node->next);
    node = node->next;
  }
}
