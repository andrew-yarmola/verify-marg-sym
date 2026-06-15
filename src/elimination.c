#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "elimination.h"

#include "relators"

//* Helper functions *//

// Crashes the program if inequalities is false
void check(bool inequalities, const char* where)
{
    if (!inequalities) {
        fprintf(stderr, "Fatal: verify error at %s\n", where);
        exit(3);
    }
}

// Replaces contents of code with the parsed word
void parse_word(char* code)
{
    char buf[MAX_CODE_LEN];
    strncpy(buf, code, MAX_CODE_LEN);
    char * start = strchr(buf,'(');
    char * end = strchr(buf,',');
    size_t len = end - start - 1;
    strncpy(code, start+1, len);
    code[len] = '\0'; 
}

// Returns a word pair encoded in code
void get_word_pair(char* code, word_pair& pair)
{
    char * start = strchr(code,'(');
    char * mid = strchr(code,',');
    char * end = strchr(code,')');
    size_t first_len = mid - start - 1;
    size_t second_len = end - mid - 1;
    strncpy(pair.first, start+1, first_len);
    strncpy(pair.second, mid+1, second_len);
    pair.first[first_len] = '\0';
    pair.second[second_len] = '\0';
}

//* Generators and words *//

SL2AJCC construct_x(const AJCCParams& params) {
    return SL2AJCC(
            params.coshL2, params.expmD2 * params.sinhL2,
            params.expD2 * params.sinhL2, params.coshL2);
};

SL2AJCC construct_y(const AJCCParams& params) {
    return SL2AJCC(
            params.coshL2, params.expD2 * params.sinhL2,
            params.expmD2 * params.sinhL2, params.coshL2);
};

// SL2AJCC matrix constrution from parameters and a word.
// Note, floating point arithmetic is not commutative and so neither is AJCC.
// We have chosen a right to left order of multiplication for validation to pass.
// Different orders of multiplication produce slightly different rounding
// errors. Since our data is greedy, this order is necessary for all words.
SL2AJCC construct_word(const AJCCParams& params, const char* word) {
    SL2AJCC w; // identity
    SL2AJCC x = construct_x(params);
    SL2AJCC y = construct_y(params);
    int len = strnlen(word, 64);
    assert(len < 64);
    int x_pow = 0;
    int y_pow = 0;	
    size_t pos;
    for (pos = len; pos > 0; --pos) {
        char h = word[pos-1];
        switch(h) {
            case 'x': ++x_pow; break;
            case 'X': --x_pow; break;
            case 'y': ++y_pow; break;
            case 'Y': --y_pow; break;
        }
        if (y_pow != 0 && x_pow != 0) {
            if (h == 'y' || h == 'Y' ) {
                w = pow(x, x_pow) * w;
                x_pow = 0;
            } else {
                w = pow(y, y_pow) * w;
                y_pow = 0;
            }
        }
    }
    // Only one of these should be true
    if (x_pow != 0) { 
        w = pow(x, x_pow) * w;
    }
    if (y_pow != 0) { 
        w = pow(y, y_pow) * w;
    }
    return w;
}

// Return the total number of x and X in word
int x_power(const char* w) {
    int count = 0;
    int len = strnlen(w, 64);
    assert(len < 64);
    for (int p = 0; p < len; ++p) {
        if (w[p] == 'x' || w[p] == 'X') ++count;
    }
    return count;
} 

// Return the total number of y and Y in word
int y_power(const char* w) {
    int count = 0;
    int len = strnlen(w, 64);
    assert(len < 64);
    for (int p = 0; p < len; ++p) {
        if (w[p] == 'y' || w[p] == 'Y') ++count;
    }
    return count;
} 

// Counts syllables in a word. A syllable to a maximal string of
// the same character ignoring case. For example xXYY has syllable legnth 2.
int syllables(const char* w) {
    int count = 0;
    int len = strnlen(w, 64);
    assert(len < 64);
    char cur = 'z'; // any char not in list
    for (int p = 0; p < len; ++p) {
        if (w[p] != tolower(cur) && w[p] != toupper(cur)) {
            ++count;
            cur = w[p];
        }
    }
    return count;
} 

// Return true if w i provably not the identity
inline const bool not_identity(const SL2AJCC& w) {
    return absLB(w.b) > 0 ||  absLB(w.c) > 0 ||
        ((absLB(w.a-1) > 0 || absLB(w.d-1) > 0) && (absLB(w.a+1) > 0 || absLB(w.d+1) > 0));
}


//* Elimination Tools *//

// Note, all validation statement are shown to hold for every point in a box

//** Parameter space bounds **//

// Our compact parameter space has the following bounds:
//     (1) sinh(L/2) >= 0
//     (2) sinh(D/2) >= 0
//     (3) 2 cosh(re(D/2)) <= 1.999 * 2
//     (4) 1.0054 <= cosh(margulis) <= 1.38 
//              note: 1.0054 < cosh(0.104) and cosh(0.846) < 1.38
// 
// Below, we group (4) into case '0' and (1)-(3) into case '1'.
// This grouping is simply a consequence of the way we ran the search.  

double g_cosh_marg_lower_bound = 1.0054;
double g_cosh_marg_upper_bound = 1.38;
double g_cosh_r_bound = 1.999;

// Return the distance the matrix w moves the point 0 + 0 i + 1 j in upper half-space.
// See Lemma TODO for the derivation of the formula.
const AJCC cosh_move_j(const SL2AJCC& w) {
    AJCC q = abs_sqrd(w.c) + abs_sqrd(w.d);
    AJCC z = w.a * conj(w.c) + w.b * conj(w.d);
    return (abs_sqrd(z) + (q - 1) * (q - 1))/(q * 2) + 1; 
}

// Verifies that box lands outisde of parameter space by valadating that
// condition (4) [code '0'] or (1)-(3) [code '1'] fail over the entire box.
void verify_out_of_bounds(const char* where, char bounds_code)
{
    Box box = build_box(where);
    switch(bounds_code) {
        case '0':	{
                        AJCC coshmu = cosh_move_j(construct_x(box.cover));
                        check(
                                absUB(coshmu) < g_cosh_marg_lower_bound ||
                                absLB(coshmu) > g_cosh_marg_upper_bound,
                                where);
                        break;
                    }
        case '1': {
                      check(
                              strictly_pos(re(-box.nearer.sinhL2)) ||
                              strictly_pos(re(-box.nearer.sinhD2)) ||
                              absLB(box.cover.twocoshreD2) > g_cosh_r_bound * 2,
                              where);
                      break;
                  }
        default: {
                     check(false, where); // crash
                 }
    }
}

//** Margulis tube collision validation **//

//*** Moved tube(y) hits tube(x) and cannot be the same ***//

//  Let tube(x) and tube(y) be the embedded Margulis tubes are x and y.
//  In this section, we validate that the given word w has the properties:
//      (1) tube(x) and w(tube(y)) intersect
//      (2) axis(x) and w(axis(y)) cannot be the same as oriented geodesiscs
//  Note, condition (2) is enough because if w maps axis(y) to axis(x) with
//  180-degree rotation, then we cannot be in a manifold group.
//  We will need three helper functions for (1) and (2).

//  Returns
//      4 cosh(real distance between axis(x) and w(axis(y))) 
//  See Lemma TODO for formula.
const AJCC four_cosh_dist_ax_way(const SL2AJCC& w, const AJCCParams& p) {
    AJCC z = ((w.a * w.a) * p.expD2  - (w.b * w.b) * p.expmD2) * p.expD2 +
        ((w.d * w.d) * p.expmD2 - (w.c * w.c) * p.expD2 ) * p.expmD2;
    return  abs(z - 2) + abs(z + 2);
}

// Returns true if axis(x) and w(axis(y)) are closer than re(D). That is, returns
// true if tube(x) and w(tube(y)) intersect. Returns false otherwise.
inline const bool moves_y_axis_too_close_to_x(const SL2AJCC& w, const AJCCParams& p) {
    AJCC diff = p.coshreD * 4 - four_cosh_dist_ax_way(w, p);
    // We know that diff is away from zero and the diff should be conj symmetrix, so
    // we only test if the real part is to one side of the bound
    return strictly_pos(diff);
}

//  Returns
//      4 sinh^2(half complex distance between axis(x) and w(axis(y))) 
//  See Lemma TODO for formula.
const AJCC four_sinh_perp2_sq_ax_way(const SL2AJCC& w, const AJCCParams& p) {
    AJCC z = ((w.a * w.a) * p.expD2  - (w.b * w.b) * p.expmD2) * p.expD2 +
        ((w.d * w.d) * p.expmD2 - (w.c * w.c) * p.expD2 ) * p.expmD2;
    return z - 2;
}

// Returns true if axis(x) and w(axis(y)) are not the same oriented geodesic.
inline const bool moved_y_axis_not_x_axis(const SL2AJCC& w, const AJCCParams& p) {
    AJCC fsp2sq = four_sinh_perp2_sq_ax_way(w, p);
    return absLB(fsp2sq) > 0; 
}

// Verifies that w(tube(y)) hits tube(x), but the axes do not coincide.
void verify_y_hits_x(const char* where, const char* word) {
    Box box = build_box(where);
    SL2AJCC w = construct_word(box.cover, word);
    check(moves_y_axis_too_close_to_x(w, box.cover) &&
            moved_y_axis_not_x_axis(w, box.cover),
            where);
}

//*** Moved tube(y) hits tube(y) and cannot be the same ***//

//  In this section, we validate that the given word w has the properties:
//      (1) tube(y) and w(tube(y)) intersect.
//          (1.1) <y, w> generate an elementray group, so the tubes intersect
//              (1.1.1) x and w fail Jorgensen's inequality
//              (1.1.2) w and x fail Jorgensen's inequality
//          (1.3) tube(y) and w(tube(y)) intersect for geometric reasons
//      (2) at least one of:
//          (2.1) syllable length of w < 4, which means there is an impossible relator
//          (2.2) axis(y) and w(axis(y)) cannot be the same as oriented geodesisc
//          (2.3) wyWY is not the identity
//  Notice that if (1) happens and <x,y> is discrete, then <y,w> is discrete elementray.
//  Since we also want <x,y> torsion-free, the only interesing cases are when w is logoxdomic
//  (i.e. a rational power of y) or the identity.  But, then we get a relator of syllable
//  length 4, which we know is impossible by (2.1). Note, if we have (2.1) or (2.3)
//  then there are no discrete points in the box.
//  We call condition (1) a variety neighborhood condition for y.

// Returns
//      4 sinh^2(half complex distance between axis(y) and w(axis(y))) 
// See Lemma TOFO for the formula.
const AJCC four_sinh_perp2_sq_ay_way(const SL2AJCC& w, const AJCCParams& p) {
    AJCC td = w.a - w.d;
    AJCC zm = w.c * p.expD2 - w.b * p.expmD2;
    // formula by using crossratios
    AJCC four_sinh_sq_perp2 = td * td - zm * zm;  
    return four_sinh_sq_perp2; 
}

//  Returns
//      4 cosh(real distance between axis(y) and w(axis(y))) 
//  See Lemma TODO for formula.
const AJCC four_cosh_dist_ay_way(const SL2AJCC& w, const AJCCParams& p) {
    AJCC four_sinh_sq_perp2 = four_sinh_perp2_sq_ay_way(w, p); 
    return abs(four_sinh_sq_perp2 + 4) + abs(four_sinh_sq_perp2);
}

// Returns true if the distance between axis(y) and w(axis(y)) is less than re(D)
inline const bool must_fix_y_axis(const SL2AJCC& w, const AJCCParams& p) {
    AJCC diff = p.coshreD * 4 - four_cosh_dist_ay_way(w, p);
    // We know that diff is away from zero and the diff should be conj symmetrix, so
    // we only test if the real part is to one side of the bound
    return strictly_pos(diff);
}

// Returns the value of Jorgensen's inequality for y, w
// See Lemma TODO for the proof of the equations below
const AJCC jorgensen_yw(const SL2AJCC& w, const AJCCParams& p) {
    AJCC shLy2 = p.sinhL2;
    AJCC td = w.a - w.d;
    AJCC z = w.c * p.expD2 - w.b * p.expmD2;
    return (abs(td * td - z * z) + 4) * abs_sqrd(shLy2);
}

// Returns the value of Jorgensen's inequality for w, y
// See Lemma TODO for the proof of the equations below
const AJCC jorgensen_wy(const SL2AJCC& w, const AJCCParams& p) {
    AJCC shLy2 = p.sinhL2;
    AJCC tr = w.a + w.d;
    AJCC td = w.a - w.d;
    AJCC z = w.c * p.expD2 - w.b * p.expmD2;
    return abs(tr * tr - 4) + abs(td * td - z * z) * abs_sqrd(shLy2);
}

// Returns true if one of the following holds
//   (1.1) <y, w> generate an elementray group, so the tubes intersect
//     (1.1.1) x and w fail Jorgensen's inequality
//     (1.1.2) w and x fail Jorgensen's inequality
//   (1.3) tube(y) and w(tube(y)) intersect for geometric reasons
inline const bool inside_var_nbd_y(const SL2AJCC& w, const AJCCParams& params) {
    return absUB(jorgensen_wy(w, params)) < 1 ||
        absUB(jorgensen_yw(w, params)) < 1 ||
        must_fix_y_axis(w, params);
}

// Returns true if axis(y) and w(axis(y)) are not the same oriented geodesic.
inline const bool cant_fix_y_axis(const SL2AJCC& w, const AJCCParams& p) {
    AJCC fsp2sq = four_sinh_perp2_sq_ay_way(w, p);
    // return absLB(fsp2sq) > 0 && absLB(fsp2sq + 4) > 0; 
    return absLB(fsp2sq) > 0; 
}

// Returns true if wvWV is not the identity
inline bool do_not_commute(const SL2AJCC& w, const SL2AJCC& v) {
    // We simply check the commutator is not the idenity in the box 
    SL2AJCC commutator = v * w * inverse(w * v);
    return not_identity(commutator); 
}

// Verifies that w(tube(y)) hits tube(y), but <y, w> cannot to be a subgroup of a discrete
// torsion free group. See heading for details. 
void verify_y_hits_y(const char* where, const char* word) {
    Box box = build_box(where);
    SL2AJCC y = construct_y(box.cover);
    SL2AJCC w = construct_word(box.cover, word);
    check(inside_var_nbd_y(w, box.cover) &&
            (syllables(word) < 4 || cant_fix_y_axis(w, box.cover) || do_not_commute(w, y)),
            where);
}

//*** Meyerhoff lower bound test ***//

// Here we verify that the maximal tube around axis(y) is smaller than
// the one guaranteed by Meyerhoff in Theorem 1 of Section 3 of
// "A Lower Bound for the Volume of Hyperbolic 3-Manifolds."

#define MAX_MEYER 7
bool meyerhoff_k_test(const AJCC& ch_o, const AJCC& cs_o, const AJCC& four_cosh_tube_rad_UB) {
    // Assumed ch and cs are real valued jets for cosh(Re(L)) and cos(Im(L))
    AJCC ch_prev = AJCC(1);
    AJCC cs_prev = AJCC(1);
    AJCC ch = ch_o;
    AJCC cs = cs_o;
    AJCC temp, four_cosh_tube_rad_LB;
    AJCC meyer_k = AJCC(1024); // arbitray large enough number
    int count = 0;
    while (absUB(ch * ch) < 2 && count < MAX_MEYER) {
        temp = ch - cs;
        if (strictly_pos(meyer_k - temp) && absUB((temp + 1) * (temp + 1)) < 2) {
            meyer_k = temp;
            // See Meyerhoff paper on volume lowerbounds for hyperbolic 3-manifolds
            four_cosh_tube_rad_LB = sqrt(-(meyer_k * 32) + 16) / meyer_k;
            if (strictly_pos(four_cosh_tube_rad_LB - four_cosh_tube_rad_UB)) {
                return true; // box can be killed
            }
        } 
        // Use Chebyshev recurrance relation
        temp = (ch_o * 2) * ch - ch_prev;
        ch_prev = ch;
        ch = temp;  
        temp = (cs_o * 2) * cs - cs_prev;
        cs_prev = cs;
        cs = temp;
        count +=1;
    }
    return false; // inconclusive
}

// Meyerhoff tube bound.
// Checks if embeded tube about axis(x) is more than (dist(axis(x), y axis(x))
// and similarly for axis(y)
void verify_meyerhoff(const char* where) {
    Box box = build_box(where);
    SL2AJCC x = construct_x(box.cover);
    AJCC four_cosh_y_tube_UB = four_cosh_dist_ay_way(x, box.cover);
    check(meyerhoff_k_test(box.cover.coshreL, box.cover.cosimL, four_cosh_y_tube_UB),
            where);
}

//** Margulis number contradiciton **// 

//*** Word moves Margulis point less than Margulis number ***//

// Our parametrization forces 1j to be the Margulis point in the upper half space
// and the Margulis number to be the distance x or y move 1j. This section validates
// that the given word w moves the Margulis point less, meaning the Margulis number is
// stricktly smaller.


// Returns true if w moves 1j less than x does over the entire box 
inline bool move_less_than_marg(const SL2AJCC& w, const AJCCParams& p) {
    AJCC diff = cosh_move_j(construct_x(p)) - cosh_move_j(w);
    return strictly_pos(diff); 
}

// Verifies all three of following:
//      (1) w moves j less than x
//      (2) w is not the identity
void verify_move(const char* where, const char* word) {
    Box box = build_box(where);
    SL2AJCC w = construct_word(box.cover, word);
    check(move_less_than_marg(w, box.cover) &&
            not_identity(w),
            where);
}

//*** Word moves tube(y) to intersect an axis of symmetry ***//

// Our parametrization has three axes of involution: (0, inf), (-1, 1), and (-i, i)
//      The involution around (0, inf) maps x -> X and y -> Y.
//      The involution around (-1, 1) maps x -> y and y -> x.
//      The involution around (-i, i) maps x -> Y and y -> X.
// In particular, if w(tube(y)) hits any of these axes and the angle is not pi/2,
// then wyW and inv(wyW) will be distinct and have a better Margulis number than x and y.

// Returns
//      2 sinh^2(half complex distance between w(axis(y)) and (0, inf)) 
// See Lemma TODO for formula
inline const AJCC two_sinh_perp2_sq_way_zero_inf(const SL2AJCC& w, const AJCCParams& p) {
    AJCC one = AJCC(1);
    return (w.b * w.d) * p.expmD2 - (w.a * w.c) * p.expD2 - one; 
}

// Returns
//      2 sinh^2(half complex distance between w(axis(y)) and (-1, 1)) 
// See Lemma TODO for formula 
inline const AJCC four_sinh_perp2_sq_way_mp_one(const SL2AJCC& w, const AJCCParams& p) {
    AJCC two = AJCC(2);
    return (w.d * w.d - w.b * w.b) * p.expmD2 + (w.a * w.a - w.c * w.c) * p.expD2 - two; 
}

// Returns
//      2 sinh^2(half complex distance between w(axis(y)) and (-i, i)) 
// See Lemma TODO for formula 
inline const AJCC four_sinh_perp2_sq_way_mp_iye(const SL2AJCC& w, const AJCCParams& p) {
    AJCC two = AJCC(2);
    AJCC iye = eye(AJCC(1));
    return ((w.d * w.d + w.b * w.b) * p.expmD2 - (w.a * w.a + w.c * w.c) * p.expD2) * iye - two; 
}

// Given input 2 sinh^2(perp/2) = z returns
//      2 cosh(re(perp)) = |z + 2| + |z|
// by the |cosh|^2 and |sinh^2| formulas. Note, here perp is meant
// to be the complex orthodistance between axes and dist = re(perp).
const AJCC two_cosh_dist(const AJCC& two_sinh_sq_perp2) {
    return abs(two_sinh_sq_perp2 + 2) + abs(two_sinh_sq_perp2);
}

// Given input 2 sinh^2(perp/2) and 2 cosh(tube radius), returns true if re(perp) < tube radius
// Note, we assume there that perp = complex distance between w(axis(y)) and an axis of symmetry
inline const bool tube_hits_axis_two(const AJCC& two_sinh_p2sq, const AJCC& two_cosh_re_tube) {
    AJCC tcd = two_cosh_dist(two_sinh_p2sq);
    // sinh(I Pi/4)^2 = -1/2 which means axes meet othrogonally
    return strictly_pos(two_cosh_re_tube - tcd) && absLB(two_sinh_p2sq + 1) > 0;
}

// Given input z = 4 sinh^2(perp/2) returns
//      4 cosh(re(perp)) = |z + 4| + |z|
// by the |cosh|^2 and |sinh^2| formulas. Note, here perp is meant
const AJCC four_cosh_dist(const AJCC& four_sinh_sq_perp2) {
    return abs(four_sinh_sq_perp2 + 4) + abs(four_sinh_sq_perp2);
}

// Given input 4 sinh^2(perp/2) and 2 cosh(tube radius), returns true if re(perp) < tube radius
// Note, we assume there that perp = complex distance between w(axis(y)) and an axis of symmetry
inline const bool tube_hits_axis_four(const AJCC& four_sinh_p2sq, const AJCC& two_cosh_re_tube) {
    AJCC fcd = four_cosh_dist(four_sinh_p2sq);
    // sinh(I Pi/4)^2 = -1/2 which means axes meet othrogonally
    return strictly_pos(two_cosh_re_tube * 2 - fcd) && absLB(four_sinh_p2sq + 2) > 0;
}

// Return true if w(tube(y)) hits, non-orthogonally, one of the three symmetry axes
inline const bool wy_hits_sym_axis(const SL2AJCC& w, const AJCCParams& p) {
    AJCC tsp2sq_inf = two_sinh_perp2_sq_way_zero_inf(w, p);
    AJCC fsp2sq_one = four_sinh_perp2_sq_way_mp_one(w, p);
    AJCC fsp2sq_iye = four_sinh_perp2_sq_way_mp_iye(w, p);
    return (tube_hits_axis_two(tsp2sq_inf, p.twocoshreD2) ||
            tube_hits_axis_four(fsp2sq_one, p.twocoshreD2) || 
            tube_hits_axis_four(fsp2sq_iye, p.twocoshreD2));
}

// Verifies that w(tube(y)) his one of the symmetry axes non-orthogonally
void verify_w_ay_hits_sym_axis(const char* where, const char* word) {
    Box box = build_box(where);
    SL2AJCC w = construct_word(box.cover, word);
    check(wy_hits_sym_axis(w, box.cover),
            where);
} 

//** Relator elimination **//

// Here we use a function that proves a given word w
// is a relator for any discrete point in the box (if any)
// To achieve this, we test the following:
//   (1) w passes the variety neighborhood condition in the box.
//          In particular, w and y commute.
//   (2) w has translation length smaller than the smallest posible
//          primitive root of y, which is computed using the Meyerhoff tube test.


// Returns 4 cosh(real_translation_length(w))) = 
//      = |trace(w)|^2 + |trace(w)^2 - 4|
// since trace(w) = 2 cosh(complex_translaton_length(w)/2)
// and |cosh(u+iv)|^2 = (cosh(2u) + cos(2v))/2
// and |sinh(u+iv)|^2 = (cosh(2u) - cos(2v))/2
const AJCC four_cosh_re_length(const SL2AJCC& w) {
    AJCC tr = w.a + w.d;
    return abs_sqrd(tr) + abs(tr*tr - 4);
}

// Given the values ch_o = cosh(re(L)) and cs_0 = cos(Im(L)) and an upper bound on an embedded tube
// around the element with translation length L, compute a lower bound on the real translation
// length of the primitive root of this element. This last part is done by using the Meyerhoff test,
// where we know a lower bound on the emebedded tube radius about a short geodesic.

#define MAX_ROOTS 2
AJCC worst_primitive_cosh_re_len(const AJCC& ch_o, const AJCC& cs_o, const AJCC& four_cosh_tube_rad_UB) {
    // Assumed ch and cs are real valued jets for cosh(Re(L)) and cos(Im(L))
    AJCC ch_prev = ch_o;
    AJCC cs_prev = cs_o;
    for (int i = 0; i < MAX_ROOTS; ++i) {
        AJCC ch = sqrt((ch_prev + 1) / 2);
        AJCC cs = sqrt((cs_prev + 1) / 2); // note, - pi <= Im(L) <= pi, so sign is +
        if (meyerhoff_k_test(ch, cs, four_cosh_tube_rad_UB)) {
            return ch_prev;
        }
        ch_prev = ch;
        cs_prev = cs;
    }
    // no luck
    AJCC zero(0);
    return zero; 
}

// Validates that word is a relator at every discrete torsion-free points in the box.
// Is is accomplished by showing that <word, y> generates an elementary group.
// And that the translation length of word is less than the primitive root of y.
// In conjuction with the torsion-free and discrete assumttions, the two facts above
// imply that word cannot be parabolic, elliptic, or loxodormic, meaning it is th identity 
bool is_proven_relator(const char* word, const AJCCParams& p) {
    SL2AJCC x = construct_x(p);
    SL2AJCC w = construct_word(p, word);
    if (x_power(word) > 0 && inside_var_nbd_y(w, p)) {
        AJCC four_cosh_y_tube_UB = four_cosh_dist_ay_way(x, p);
        AJCC cosh_prim_re_len = worst_primitive_cosh_re_len(p.coshreL, p.cosimL, four_cosh_y_tube_UB); 
        AJCC diff = cosh_prim_re_len * 4 - four_cosh_re_length(w);
        if (strictly_pos(diff)) {
            return true;
        }      
    }
    return false;
}

//*** Impossible relators ***//

// Here we check that the given word is (1) a proven relator and
// (2) is a word that is impossible by means of analysis in Lemma TODO

inline bool is_impossible(const char* word) {
    int len = sizeof(impossible)/sizeof(impossible[0]);
    assert(len == 151);
    for (int i = 0; i < len; ++i) {
        if (strncmp(word, impossible[i], 32) == 0) {
            return true;
        }
    }
    return false;
}

// Verifies that the word is (1) on the impossible list and (2) is a proven relator
void verify_impossible_relator(const char* where, const char* word) {
    Box box = build_box(where);
    check(is_impossible(word) &&
            is_proven_relator(word, box.cover),
            where); 
}

//*** Weeks relators ***//

// Symmetric relators are special in that the group <x, y| w, inv(w)> is a known
// closed 3-manifold group. So, if w is a proven relator, then so is inv(w) and we
// have idenitified a subgroup of the group generated by x,y. In all cases,
// this group is provably the Weeks manifold, so by volumes of representations,
// it follows that x,y generate the Weeks manifold (at the discrete torsion free points)

// Checks tha the word is on the list of Weeks relators
// See Lemma TODO for the proof of why these relators are Weeks
inline bool is_weeks_relator(const char* word) {
    int len = sizeof(weeks)/sizeof(weeks[0]);
    assert(len == 4);
    for (int i = 0; i < len; ++i) {
        if (strncmp(word, weeks[i], 32) == 0) {
            return true;
        }
    }
    return false;
}

// Verifies that the word is (1) on the symmetirc list and (2) a relator. 
void verify_weeks(const char* where, const char* word) {
    Box box = build_box(where);
    check(is_weeks_relator(word) &&
            is_proven_relator(word, box.cover),
            where); 
}

//*** Vol3 relators ***//

// We check that XYXYxYXYXy and yXYxYxyxYxYY are proven relators
// for the box. By Lemma TODO, this means that vol3 is a subgroup of the group
// generated by x,y at any discrete point. Again, volume considerations imply that
// any discrete torsion free point must be vol3 on the nose.
void verify_vol3(const char* where, const char* first, const char* second) {
    Box box = build_box(where);
    check((
           (strncmp(first, "XYXyXyxyXy", 32) == 0 &&
            strncmp(second, "XYXYxYXYXy", 32) == 0) ||
           (strncmp(first, "XYXyXyxyXy", 32) == 0 &&
            strncmp(second, "XYXyXYXYxY", 32) == 0) ||
           (strncmp(first, "XyXYXYxYXY", 32) == 0 &&
            strncmp(second, "XYXyXyxyXy", 32) == 0)
          ) &&
          is_proven_relator(first, box.cover) &&
          is_proven_relator(second, box.cover),
          where); 
}
