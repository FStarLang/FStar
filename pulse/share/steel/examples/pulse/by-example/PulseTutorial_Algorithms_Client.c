#include "PulseTutorial_Algorithms.h"

int main(int argc, char **argv) {
  uint32_t votes[4] = {1, 1, 0, 1};
  FStar_Pervasives_Native_option__uint32_t result = PulseTutorial_Algorithms_majority__uint32_t(votes, 4);
  if (result.tag == FStar_Pervasives_Native_None) {
    printf("No majority\n");
  } else {
    printf("Majority: %d\n", result.v);
  }
  return 0;
}