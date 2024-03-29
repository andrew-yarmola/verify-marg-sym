#ifndef _elimination_h_
#define _elimination_h_
#include "box.h"
#include "arithmetic/SL2.h"

#define MAX_DEPTH 256
#define MAX_CODE_LEN 512

// Helper functions

void check(bool inequalities, const char* where);

void parse_word(char* code);

typedef struct {
    char first[MAX_CODE_LEN];
    char second[MAX_CODE_LEN];
} word_pair;

void get_word_pair(char* code, word_pair& pair);

// Elimination functions

SL2AJCC construct_x(const AJCCParams& params);

SL2AJCC construct_y(const AJCCParams& params);

SL2AJCC construct_word(const AJCCParams& params, const char* word);

void verify_out_of_bounds(const char* where, char bounds_code);

void verify_meyerhoff(const char* where);

void verify_y_hits_x(const char* where, const char* word);

void verify_y_hits_y(const char* where, const char* word);

void verify_move(const char* where, const char* word);

void verify_w_ay_hits_sym_axis(const char* where, const char* word);

void verify_impossible_relator(const char* where, const char* word);

void verify_weeks(const char* where, const char* word);

void verify_vol3(const char* where, const char* first, const char* second);

#endif // _elimination_h_
