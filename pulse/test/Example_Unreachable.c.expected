/* krml header omitted for test repeatability */


#include "Example_Unreachable.h"

bool Example_Unreachable_test(FStar_Pervasives_Native_option__bool x)
{
  if (x.tag == FStar_Pervasives_Native_Some)
    return x.v;
  else if (x.tag == FStar_Pervasives_Native_None)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

