#ifndef _box_h_
#define _box_h_
#include "arithmetic/AJCC.h"

// Our root box has center (0,0,0,0) and sides of length
// 2 * (2, 2^(3/4), 2^(2/4), 2^(1/4)). The last is > 2.37
#define DIM 4
#define SCL 2

// Params datatype at the center
typedef struct {
  XComplex sinhL2;
  XComplex sinhD2;
} XParams;

// Params datatype for affine-jet computations
typedef struct {
  AJCC sinhL2;
  AJCC sinhD2;
  // derived parameters from the two above
  AJCC sinhsqL2;
  AJCC sinhsqD2;
  AJCC coshsqL2;
  AJCC coshsqD2;
  AJCC coshL2;
  AJCC coshD2;
  AJCC expD2;
  AJCC expmD2;
  AJCC twocoshreD2;
  AJCC twosinhreD2;
  AJCC coshreD;
  AJCC coshreL;
  AJCC sinhreL;
  AJCC cosimL;
} AJCCParams;

typedef struct {
  double center_digits[DIM];
  double size_digits[DIM];
  double center[DIM];
  double size[DIM];
  AJCCParams cover;
  XParams nearer; // all values closer to 0 than in box or 0 if box overlaps
} Box;

Box build_box(const char* where);

void print_box(const Box& box);

#endif // _box_h_
