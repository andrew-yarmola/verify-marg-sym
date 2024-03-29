#include <stdlib.h>
#include "elimination.h"

void verify(char* where, size_t depth, size_t* count_ptr)
{
    check(depth < MAX_DEPTH, where);
    *count_ptr += 1;
    char code[MAX_CODE_LEN];
    fgets(code, MAX_CODE_LEN, stdin);
    switch(code[0]) {
        case 'X': { 
            *count_ptr -= 1; // don't count branch nodes
            where[depth] = '0';
            where[depth + 1] = '\0';
            verify(where, depth + 1, count_ptr);
            where[depth] = '1';
            where[depth + 1] = '\0';
            verify(where, depth + 1, count_ptr);
            break; }
        case '0':
        case '1': { 
            verify_out_of_bounds(where, code[0]);
            break; }
        case 'A': { // Line has format  A(word) - killed_y_hits_x
            parse_word(code);
            verify_y_hits_x(where, code);
            break; }
        case 'Y': { // Line has format  Y(word) - killed_y_hits_y 
            parse_word(code);
            verify_y_hits_y(where, code);
            break; }
        case '2': { 
            verify_meyerhoff(where);
            break; }
        case 'M': { // Line has format  M(word) - killed_move
            parse_word(code);
            verify_move(where, code);
            break; }
        case 'N': { // Line has format  N(word) - killed_w_ay_hits_sym_axis
            parse_word(code);
            verify_w_ay_hits_sym_axis(where, code);
            break; }
        case 'E': { // Line has format  E(word) - killed_impossible_relator
            parse_word(code);
            verify_impossible_relator(where, code);
            break; }
        case 'S': { // Line has format  S(word) - verified_symmetric_relator
            parse_word(code);
            verify_weeks(where, code);
            break; }
        case 'T': { // Line has format  T(first, second) - verified_vol3_relator_pair
            word_pair pair;
            get_word_pair(code, pair);
            verify_vol3(where, pair.first, pair.second);
            break; }
        // We fail by default, guaranteeing completes of the tree
        default: {
            check(false, where);
        }
    }
    // Block below is only for printing progress. 
    //    progress bar code from: https://stackoverflow.com/a/36315819/1411737
    if (*count_ptr % (1 << 18) == 0 && code[0] != 'X') {
        #define PBSTR "++++++++++++++++++++++++++++++++++++++++++++++++++"
        #define PBWIDTH 50
        #define NUM_NODES 52726055 
        double fraction = ((double) *count_ptr) / NUM_NODES;
        int lpad = (int) (fraction * PBWIDTH);
        int rpad = PBWIDTH - lpad;
        printf("\r%6.2f%% [%.*s%*s] of %d", 100 * fraction, lpad, PBSTR, rpad, "", NUM_NODES);
        fflush(stdout);
    }
    if (depth == 0) {
        printf("\r%6.2f%% [%s] of %d\n", 100.00, PBSTR, NUM_NODES);
    }
}

int main(int argc, char**argv)
{
    if(argc != 1) {
        fprintf(stderr,"Usage: %s < data\n", argv[0]);
        exit(1);
    }
    char where[MAX_DEPTH];
    size_t depth = 0;
    where[depth] = '\0';

    printf("Begin verify %s - {\n", where);
    initialize_roundoff();
    size_t count = 0;
    verify(where, depth, &count);
    if(!roundoff_ok()){
        printf(". underflow may have occurred\n");
        exit(1);
    }
    printf("Successfully verified all %lu nodes\n", count);
    printf("}.\n");
    exit(0);
}
