/*
** Copyright (C) 2015 Martin Brain
** 
** This program is free software: you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation, either version 3 of the License, or
** (at your option) any later version.
** 
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
** 
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
** test.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 06/08/14
**
** The main loop of the test program
**
*/

#include <math.h>
#include <ieee754.h>
#include <fenv.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>

#include "symfpu/baseTypes/simpleExecutable.h"

#include "symfpu/applications/executable.h"


/*** Test Vector Generation ***/

#define NUMBER_OF_FLOAT_TESTS 120
static float floatTestValue [NUMBER_OF_FLOAT_TESTS] = {
  0x0p+0f, -0x0p+0f,                        // Zeros
  0x1p+0f, -0x1p+0f,                        // Ones
  INFINITY, -INFINITY, NAN, -NAN,           // Special values
  M_E, M_LOG2E, M_LOG10E, M_LN2, M_LN10,    // Mathematical constants
  M_PI, M_PI_2, M_PI_4, M_1_PI, M_2_PI,
  M_2_SQRTPI, M_SQRT2, M_SQRT1_2,
   0x1.fffffcp-127,  0x1.000004p-127,  0x1p-127,  0x1p-148,  0x1p-149,  // Subnormals
  -0x1.fffffcp-127, -0x1.000004p-127, -0x1p-127, -0x1p-148, -0x1p-149,
   0x1.ffffffcp-103,  0x1.ffffffcp-99,  0x1.ffffffcp-75,      // Normals
   0x1.ffffffcp-51,   0x1.ffffffcp-27,  0x1.ffffffcp-03,
   0x1.ffffffcp+51,   0x1.ffffffcp+27,  0x1.ffffffcp+03,
   0x1.ffffffcp+103,  0x1.ffffffcp+99,  0x1.ffffffcp+75,
  -0x1.ffffffcp-103, -0x1.ffffffcp-99, -0x1.ffffffcp-75,
  -0x1.ffffffcp-51,  -0x1.ffffffcp-27, -0x1.ffffffcp-03,
  -0x1.ffffffcp+51,  -0x1.ffffffcp+27, -0x1.ffffffcp+03,
  -0x1.ffffffcp+103, -0x1.ffffffcp+99, -0x1.ffffffcp+75,
   0x1.fffffep+127,                                            // From the CBMC regression tests
   0x1.4p+4,
   0x1.fffffep-105f,
   0x1.0p-23,
   0x1.0p-126f,
   0x1.fffffep-3f,
   0x1.fffffep+123f,
   0x1.000002p+124f,
   0x1.0p+124f,
   0x1.fffffep-3f,
   0x1p+124f,
   0x1p-126f,
   0x1.000000p-63f,
   0x1.fffffep-64f,
   0x1.084c64p-63f,
   0x1.efec9ep-64f,
   0x1.47e8c2p-63f,
   0x1.8fb86cp-64f,
   0x1.1fcf1cp-63f,
   0x1.c769c0p-64f,
   0x1.b1fffcp-63f,
   0x1.2e025ep-64f,
   0x1.000000p-62f,
   0x1.fffffep-65f,
   0x1.000000p-61f,
   0x1.fffffep-66f,
   0x1.000000p-50f,
   0x1.fffffep-77f,
   0x1.000000p-30f,
   0x1.fffffep-97f,
   0x1.000000p-10f,
   0x1.fffffep-117f,
   0x1.000000p-1f,
   0x1.fffffep-126f,
   0x1.9e0c22p-101f,
  -0x1.3c9014p-50f,
   0x1.8p-24,
   0x1.fffffep-1f,
   0x1.000002p+0f,
   0x1.7ffffep-24f,
   0x1.800002p-24f,
   0x1.800000p-24f,
  -0x1.0p-127f,
  -0x1.6b890ep+29,
   0x1.6b890ep+29,
   0x1.000002p+25f,
   0x1.000004p+25f,
   0x1.0017ecp+22f,            // Divide!
   0x1.7ffff8p+21f,
   0x1.557542p+0f,
   0x1p+120f,                  // Distributivity
  -0x1p+120f,
   0x1.46p+7f,                 // e^{pi * sqrt{163}} = 640320^3 + 744
   0x1.38a8p+19f,
   0x1.74p+9f,
   0x1.79999ap+5f,             // 47.2
   0x1.99999ap-4f,             // For the patriots..
   0x1.5p+5f,
   0x1.7p+4f,
   0x1.fffffep+24,             // To test carry on increment
   0x1.fffffcp+24,
   0x1.0p-1,                   // Half for a laugh
   0x1.000002p-75f,            // To test rounding on multiply
   0x1.0p-75f
};

float getTestValue (uint64_t index) {
  if (index < NUMBER_OF_FLOAT_TESTS) {
    return floatTestValue[index];
  } else {
    index -= NUMBER_OF_FLOAT_TESTS;

    ieee754_float c;

    // The low bits give the sign and exponent so that a wide range is covered quickly
    c.ieee.negative = index & 0x1;
    index >>= 1;

    c.ieee.exponent = ((index & 0xFE) >> 1) | ((index & 0x1) << 7);
    index >>= 8;

    assert(index < (1 << 23));

    // Use the next bit to optionally negates the word
    //index = (index & 0x1) ? ~(index >> 1) : (index >> 1);

    // Even bits affect the MSBs of the significand, odd bits affect the LSBs of the significand
    uint32_t lsb = 0x0;
    uint32_t msb = 0x0;


    for (uint32_t i = 0; i < 23; ++i) {
      if (i & 0x1) {
        lsb |= (((index >> i) & 0x1) << (i >> 1));
      } else {
        msb <<= 1;
        msb |= ((index >> i) & 0x1);
      }
    }

    assert((lsb & (msb << 11)) == 0);

    c.ieee.mantissa = lsb | (msb << 11);

    return c.f;
  }
}




/*** Types ***/

// We are testing the 'simple executable' back-end
typedef symfpu::simpleExecutable::traits traits;
typedef traits::fpt fpt;
typedef traits::rm rm;

// We are also testing it only for single precision
traits::fpt singlePrecision(8,24);

// Which means we need the test infrastructure configured for both
typedef executableTests<uint32_t, float, traits> test;






/*** Test Execution ***/


typedef uint32_t (*unaryFunctionTFP) (const fpt &, uint32_t);


void unaryFunctionTest (int verbose, uint64_t start, uint64_t end, unaryFunctionTFP test, unaryFunctionTFP ref) {
  uint64_t i;

  for (i = start; i < end; ++i) {
      float f = getTestValue(i);
      
      uint32_t input = *((uint32_t *)(&f));
     
      uint32_t reference = ref(singlePrecision, input);
      uint32_t computed = test(singlePrecision, input);
      
      if (verbose || !test::smtlibEqualReference(singlePrecision, computed, reference)) {
	fprintf(stdout,"vector[%d] ", (uint32_t)i);
	fprintf(stdout,"input = 0x%x, computed = 0x%x, real = 0x%x\n", input, computed, reference);
	fflush(stdout);
      }

      if ((i & 0xFFFF) == 0) {
	fprintf(stdout,".");
	fflush(stdout);
      }
  }

  return;
}



typedef bool (*unaryPredicateTFP) (const fpt &, uint32_t);

void unaryPredicateTest (int verbose, uint64_t start, uint64_t end, unaryPredicateTFP test, unaryPredicateTFP ref) {
  uint64_t i;

  for (i = start; i < end; ++i) {
      float f = getTestValue(i);
      
      uint32_t input = *((uint32_t *)(&f));
     
      bool reference = ref(singlePrecision, input);
      bool computed = test(singlePrecision, input);
      
      if (verbose || !(computed == reference)) {
	fprintf(stdout,"vector[%d] ", (uint32_t)i);
	fprintf(stdout,"input = 0x%x, computed = %d, real = %d\n", input, computed, reference);
	fflush(stdout);
      }

      if ((i & 0xFFFF) == 0) {
	fprintf(stdout,".");
	fflush(stdout);
      }
  }

  return;
}


uint64_t splitRight (uint64_t input) {
  uint64_t output = 0;

  for (uint64_t i = 0; i <= 63; i +=2) {
    output |= (input & (1ULL << i)) ? 1ULL << (i >> 1ULL) : 0;
  }

  return output;
}

uint64_t splitLeft (uint64_t input) {
  uint64_t output = 0;

  for (uint64_t i = 1; i <= 63; i +=2) {
    output |= (input & (1ULL << i)) ? 1ULL << (i >> 1ULL) : 0;
  }

  return output;
}


typedef bool (*binaryPredicateTFP) (const fpt &, uint32_t, uint32_t);

void binaryPredicateTest (int verbose, uint64_t start, uint64_t end, binaryPredicateTFP test, binaryPredicateTFP ref) {
  uint64_t i;

  for (i = start; i < end; ++i) {
    uint64_t right = splitRight(i);
    uint64_t left = splitLeft(i);

    float f = getTestValue(right);
    float g = getTestValue(left);
    
    uint32_t input1 = *((uint32_t *)(&f));
    uint32_t input2 = *((uint32_t *)(&g));
    
    bool reference = ref(singlePrecision, input1, input2);
    bool computed = test(singlePrecision, input1, input2);
    
    if (verbose || !(computed == reference)) {
      fprintf(stdout,"vector[%d -> (%d,%d)] ", (uint32_t)i, (uint32_t)left, (uint32_t)right);
      fprintf(stdout,"input1 = 0x%x, input2 = 0x%x, computed = %d, real = %d\n", input1, input2, computed, reference);
      fflush(stdout);
    }
    
    if ((i & 0xFFFF) == 0) {
      fprintf(stdout,".");
      fflush(stdout);
    }
  }
  
  return;
}








typedef uint32_t (*binaryFunctionTFP) (const fpt &, const rm &, uint32_t, uint32_t);

void binaryFunctionTest (int verbose, uint64_t start, uint64_t end, const rm &roundingMode, binaryFunctionTFP test, binaryFunctionTFP ref) {
  uint64_t i;

  for (i = start; i < end; ++i) {
    uint64_t right = splitRight(i);
    uint64_t left = splitLeft(i);

    float f = getTestValue(right);
    float g = getTestValue(left);
    
    uint32_t input1 = *((uint32_t *)(&g));
    uint32_t input2 = *((uint32_t *)(&f));
    
    uint32_t reference = ref(singlePrecision, roundingMode, input1, input2);
    uint32_t computed = test(singlePrecision, roundingMode, input1, input2);

    if (verbose || !test::smtlibEqualReference(singlePrecision, computed, reference)) {
      fprintf(stdout,"vector[%d -> (%d,%d)] ", (uint32_t)i, (uint32_t)left, (uint32_t)right);
      fprintf(stdout,"input1 = 0x%x, input2 = 0x%x, computed = 0x%x, real = 0x%x\n", input1, input2, computed, reference);
      fflush(stdout);
    }

    if ((i & 0xFFFF) == 0) {
      fprintf(stdout,".");
      fflush(stdout);
    }
  }
  
  return;
}





struct unaryFunctionTestStruct {
  int enable;
  const char *name;
  unaryFunctionTFP test;
  unaryFunctionTFP ref;
};

struct unaryPredicateTestStruct {
  int enable;
  const char *name;
  unaryPredicateTFP test;
  unaryPredicateTFP ref;
};

struct binaryPredicateTestStruct {
  int enable;
  const char *name;
  binaryPredicateTFP test;
  binaryPredicateTFP ref;
};

struct binaryFunctionTestStruct {
  int enable;
  const char *name;
  binaryFunctionTFP test;
  binaryFunctionTFP ref;
};

struct roundingModeTestStruct {
  int enable;
  const char *name;
  rm *roundingMode;
};





/*** Application ***/



#define INCREMENT 0xFFFFFF

int main (int argc, char **argv) {
  struct unaryFunctionTestStruct unaryFunctionTests[] = {
    {0, "unpackPack", test::unpackPack, test::unpackPackReference},
    {0,     "negate",     test::negate,     test::negateReference},
    {0,   "absolute",   test::absolute,   test::absoluteReference},
    {0,         NULL,             NULL,                      NULL}
  };

  struct unaryPredicateTestStruct unaryPredicateTests[] = {
    {0,    "isNormal",    test::isNormal,    test::isNormalReference},
    {0, "isSubnormal", test::isSubnormal, test::isSubnormalReference},
    {0,      "isZero",      test::isZero,      test::isZeroReference},
    {0,  "isInfinite",  test::isInfinite,  test::isInfiniteReference},
    {0,       "isNaN",       test::isNaN,       test::isNaNReference},
    {0,  "isPositive",  test::isPositive,  test::isPositiveReference},
    {0,  "isNegative",  test::isNegative,  test::isNegativeReference},
    {0,          NULL,              NULL,                       NULL}
  };

  struct binaryPredicateTestStruct binaryPredicateTests[] = {
    {0,      "SMT-LIB equal",     test::smtlibEqual,     test::smtlibEqualReference},
    {0,       "IEE754 equal",    test::ieee754Equal,    test::ieee754EqualReference},
    {0,          "less than",        test::lessThan,        test::lessThanReference},
    {0, "less than or equal", test::lessThanOrEqual, test::lessThanOrEqualReference},
    {0,                 NULL,                  NULL,                           NULL}
  };

  struct binaryFunctionTestStruct binaryFunctionTests[] = {
    {0, "multiply",  test::multiply, test::multiplyReference},
    {0,      "add",       test::add,      test::addReference},
    {0, "subtract",       test::sub,      test::subReference},
    {0,       NULL,            NULL,                    NULL}
  };

  struct roundingModeTestStruct roundingModeTests[] = {
    {0, "RNE", new traits::rm(traits::RNE())},
    {0, "RTP", new traits::rm(traits::RTP())},
    {0, "RTN", new traits::rm(traits::RTN())},
    {0, "RTZ", new traits::rm(traits::RTZ())},
  //{0, "RNA", new traits::rm(traits::RNA())},   // Disabled until a suitable reference is available
    {0,  NULL,         NULL}
  };

  uint64_t start = 0;
  uint64_t end = INCREMENT;
  int verbose = 0;
  int help = 0;
  int enableAllTests = 0;
  int enableAllRoundingModes = 0;
  int continuous = 0;

  struct option options[] = {
    {         "verbose",        no_argument,                          &verbose,  1 },
    {            "help",        no_argument,                             &help,  1 },
    {           "start",  required_argument,                              NULL, 's'},
    {             "end",  required_argument,                              NULL, 'e'},
    {      "continuous",        no_argument,                       &continuous,  1 },
    {        "allTests",        no_argument,                   &enableAllTests,  1 },
    {"allRoundingModes",        no_argument,           &enableAllRoundingModes,  1 },
    {      "unpackPack",        no_argument,   &(unaryFunctionTests[0].enable),  1 },
    {          "negate",        no_argument,   &(unaryFunctionTests[1].enable),  1 },
    {        "absolute",        no_argument,   &(unaryFunctionTests[2].enable),  1 },
    {        "isNormal",        no_argument,  &(unaryPredicateTests[0].enable),  1 },
    {     "isSubnormal",        no_argument,  &(unaryPredicateTests[1].enable),  1 },
    {          "isZero",        no_argument,  &(unaryPredicateTests[2].enable),  1 },
    {      "isInfinite",        no_argument,  &(unaryPredicateTests[3].enable),  1 },
    {           "isNaN",        no_argument,  &(unaryPredicateTests[4].enable),  1 },
    {      "isPositive",        no_argument,  &(unaryPredicateTests[5].enable),  1 },
    {      "isNegative",        no_argument,  &(unaryPredicateTests[6].enable),  1 },
    {     "smtlibEqual",        no_argument, &(binaryPredicateTests[0].enable),  1 },
    {    "ieee754Equal",        no_argument, &(binaryPredicateTests[1].enable),  1 },
    {        "lessThan",        no_argument, &(binaryPredicateTests[2].enable),  1 },
    { "lessThanOrEqual",        no_argument, &(binaryPredicateTests[3].enable),  1 },
    {             "rne",        no_argument,    &(roundingModeTests[0].enable),  1 },
    {             "rtp",        no_argument,    &(roundingModeTests[1].enable),  1 },
    {             "rtn",        no_argument,    &(roundingModeTests[2].enable),  1 },
    {             "rtz",        no_argument,    &(roundingModeTests[3].enable),  1 },
  //{             "rna",        no_argument,    &(roundingModeTests[4].enable),  1 },
    {             "RNE",        no_argument,    &(roundingModeTests[0].enable),  1 },
    {             "RTP",        no_argument,    &(roundingModeTests[1].enable),  1 },
    {             "RTN",        no_argument,    &(roundingModeTests[2].enable),  1 },
    {             "RTZ",        no_argument,    &(roundingModeTests[3].enable),  1 },
  //{             "RNA",        no_argument,    &(roundingModeTests[4].enable),  1 },
    {        "multiply",        no_argument,  &(binaryFunctionTests[0].enable),  1 },
    {             "add",        no_argument,  &(binaryFunctionTests[1].enable),  1 },
    {        "subtract",        no_argument,  &(binaryFunctionTests[2].enable),  1 },
    {              NULL,                  0,                              NULL,  0 }
  }; 

  bool parseOptions = true;
  while (parseOptions) {
    int currentOption = 0;
    int response = getopt_long(argc, argv, "vs:e:", options, &currentOption);

    switch(response) {
    case 'v' :
      verbose = 1;
      break;

    case 's' :
      start = strtoull(optarg,NULL,0);
      break;

    case 'e' :
      end = strtoull(optarg,NULL,0);
      break;

    case 0 :    /* Flag set */
      break;

    case -1 :   /* End of options */
      parseOptions = false;
      break;

    case '?' :  /* Unknown option */
      fprintf(stderr,"Unknown option : \"%s\"\n", optarg);
      return 1;
      break;

    default :   /* Unrecognised getopt response */
      fprintf(stderr,"Unrecognised getopt response \'%d\' from \"%s\"\n",response, optarg);
      return 1;
      break;
    }
  }

  /* Help text */
  if (help) {
    fprintf(stderr, "TODO: Super helpful message here!\n");

    fprintf(stderr, "Options : \n");
    struct option *opt = &(options[0]);
    while (opt->name != NULL) {
      switch (opt->has_arg) {
      case no_argument : fprintf(stderr, "\t--%s\n", opt->name); break;
      case required_argument : fprintf(stderr, "\t--%s\t  argument\n", opt->name); break;
      case optional_argument : fprintf(stderr, "\t--%s\t[ argument ]\n", opt->name); break;
      default :	fprintf(stderr, "\t--%s\t???\n", opt->name); break;
      }

      ++opt;
    }

    return 0;
  }

  int roundingModeSet = 0;
  uint64_t j = 0;
  while (roundingModeTests[j].name != NULL) {
    roundingModeSet |= roundingModeTests[j].enable;
    ++j;
  }
  if (!roundingModeSet && !enableAllRoundingModes) {
    // Set default rounding mode of RNE
    roundingModeTests[0].enable = 1;
  }


 top :

  /* Unary function tests */
  int i = 0;
  while (unaryFunctionTests[i].name != NULL) {
    if (enableAllTests || unaryFunctionTests[i].enable) {
      fprintf(stdout, "Running unary test for %s : ", unaryFunctionTests[i].name);
      fflush(stdout);

      unaryFunctionTest(verbose, start, end, unaryFunctionTests[i].test, unaryFunctionTests[i].ref);

      fprintf(stdout, "\n");
      fflush(stdout);
    }
    i++;
  }
  fprintf(stdout, "All unary function tests complete.\n\n");


  /* Unary predicate tests */
  i = 0;
  while (unaryPredicateTests[i].name != NULL) {
    if (enableAllTests || unaryPredicateTests[i].enable) {
      fprintf(stdout, "Running unary test for %s : ", unaryPredicateTests[i].name);
      fflush(stdout);

      unaryPredicateTest(verbose, start, end, unaryPredicateTests[i].test, unaryPredicateTests[i].ref);

      fprintf(stdout, "\n");
      fflush(stdout);
    }
    i++;
  }
  fprintf(stdout, "All unary predicate tests complete.\n\n");


  /* Binary predicate tests */
  i = 0;
  while (binaryPredicateTests[i].name != NULL) {
    if (enableAllTests || binaryPredicateTests[i].enable) {
      fprintf(stdout, "Running binary test for %s : ", binaryPredicateTests[i].name);
      fflush(stdout);

      binaryPredicateTest(verbose, start, end, binaryPredicateTests[i].test, binaryPredicateTests[i].ref);

      fprintf(stdout, "\n");
      fflush(stdout);
    }
    i++;
  }
  fprintf(stdout, "All binary predicate tests complete.\n\n");


  /* Binary function tests */
  i = 0;
  while (binaryFunctionTests[i].name != NULL) {
    if (enableAllTests || binaryFunctionTests[i].enable) {

      j = 0;
      while (roundingModeTests[j].name != NULL) {
	if (enableAllRoundingModes || roundingModeTests[j].enable) {
	  fprintf(stdout, "Running binary test for %s %s : ", binaryFunctionTests[i].name, roundingModeTests[j].name);
	  fflush(stdout);

	  binaryFunctionTest(verbose, start, end, *(roundingModeTests[j].roundingMode), binaryFunctionTests[i].test, binaryFunctionTests[i].ref);

	  fprintf(stdout, "\n");
	  fflush(stdout);
	}
	j++;
      }
    }
    i++;
  }
  fprintf(stdout, "All binary function tests complete.\n\n");


  if (continuous) {
    end += INCREMENT;
    goto top;
  }


  return 1;
}
