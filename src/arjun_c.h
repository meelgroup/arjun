/******************************************
Copyright (C) 2024 Authors of Arjun, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

/*
 * Pure C ABI for Arjun (SimplifiedCNF + standalone preprocessing).
 *
 * Variables are 0-indexed; clause literals use DIMACS convention (signed
 * nonzero ints, |lit|-1 is the variable, sign = negation).
 *
 * Functions that may fail return int (0 = success) and set a thread-local
 * error string (arjun_last_error()); pointer-returning ones return NULL.
 */

#ifndef ARJUN_C_H
#define ARJUN_C_H

#include <stdint.h>
#include <stddef.h>
#include <gmp.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque types. */
typedef struct arjun_fgen      arjun_fgen_t;
typedef struct arjun_field     arjun_field_t;
typedef struct arjun_simpcnf   arjun_simpcnf_t;
typedef struct arjun_arjun     arjun_arjun_t;

/* Field-kind discriminator for arjun_field_t. */
typedef enum {
    ARJUN_FIELD_MPZ = 0,  /* integer  (FMpz / FGenMpz) */
    ARJUN_FIELD_MPQ = 1   /* rational (FMpq / FGenMpq) */
} arjun_field_kind;

/* ----------------------------------------------------------------- */
/* Error handling                                                    */
/* ----------------------------------------------------------------- */

/* Returns the message from the most recent failing call on the current
 * thread, or "" if none. Owned by arjun; do not free. */
const char* arjun_last_error(void);

/* ----------------------------------------------------------------- */
/* FieldGen                                                          */
/* ----------------------------------------------------------------- */

arjun_fgen_t* arjun_fgen_mpz_new(void);
arjun_fgen_t* arjun_fgen_mpq_new(void);
void          arjun_fgen_free(arjun_fgen_t* fg);
arjun_field_kind arjun_fgen_kind(const arjun_fgen_t* fg);

/* ----------------------------------------------------------------- */
/* Field                                                             */
/* ----------------------------------------------------------------- */

/* Construct a Field with the value 0 or 1. */
arjun_field_t* arjun_field_zero(const arjun_fgen_t* fg);
arjun_field_t* arjun_field_one (const arjun_fgen_t* fg);

/* Construct directly with a small integer value (signed).
 * The kind of the field follows the FieldGen's kind. */
arjun_field_t* arjun_field_from_int(const arjun_fgen_t* fg, long val);

/* Construct an MPQ field from a GMP mpq_t. Requires fg to be MPQ.
 * The value of in is copied; caller retains ownership of in. */
arjun_field_t* arjun_field_from_mpq(const arjun_fgen_t* fg, const mpq_t in);

/* Construct an MPZ field from a GMP mpz_t. Requires fg to be MPZ. */
arjun_field_t* arjun_field_from_mpz(const arjun_fgen_t* fg, const mpz_t in);

void              arjun_field_free(arjun_field_t* f);
arjun_field_t*    arjun_field_dup (const arjun_field_t* f);
arjun_field_kind  arjun_field_kind_of(const arjun_field_t* f);
int               arjun_field_is_zero(const arjun_field_t* f);
int               arjun_field_is_one (const arjun_field_t* f);

/* Copy out the underlying GMP value. The caller must mpz_init/mpq_init
 * the destination before calling. Returns 0 on success, -1 if the field's
 * kind doesn't match. */
int arjun_field_get_mpz(const arjun_field_t* f, mpz_t out);
int arjun_field_get_mpq(const arjun_field_t* f, mpq_t out);

/* In-place arithmetic: *a := *a OP *b. a and b must have the same kind. */
int arjun_field_mul_assign(arjun_field_t* a, const arjun_field_t* b);
int arjun_field_add_assign(arjun_field_t* a, const arjun_field_t* b);
int arjun_field_sub_assign(arjun_field_t* a, const arjun_field_t* b);

/* ----------------------------------------------------------------- */
/* SimplifiedCNF                                                     */
/* ----------------------------------------------------------------- */

arjun_simpcnf_t* arjun_simpcnf_new(const arjun_fgen_t* fg);
void             arjun_simpcnf_free(arjun_simpcnf_t* c);

/* Append n new variables. */
void   arjun_simpcnf_new_vars(arjun_simpcnf_t* c, uint32_t n);
uint32_t arjun_simpcnf_nvars(const arjun_simpcnf_t* c);

/* Add a clause. lits: array of n_lits DIMACS-style nonzero ints.
 * Returns 0 on success, -1 on error (zero literal, var out of range). */
int arjun_simpcnf_add_clause    (arjun_simpcnf_t* c, const int32_t* lits, size_t n_lits);
int arjun_simpcnf_add_red_clause(arjun_simpcnf_t* c, const int32_t* lits, size_t n_lits);

/* Enable weighted counting. Required before set_lit_weight. */
void arjun_simpcnf_set_weighted(arjun_simpcnf_t* c, int weighted);
int  arjun_simpcnf_get_weighted(const arjun_simpcnf_t* c);

/* Set the weight on a DIMACS literal (signed). The field is borrowed (the
 * value is copied). The field's kind must match the SimplifiedCNF's. */
int arjun_simpcnf_set_lit_weight(arjun_simpcnf_t* c, int32_t lit,
                                 const arjun_field_t* weight);

/* Set the sampling (independent) variable set. vars: 0-indexed variable
 * indices, each in [0, nvars). May only be called once. */
int arjun_simpcnf_set_sampl_vars(arjun_simpcnf_t* c,
                                 const uint32_t* vars, size_t n_vars);

/* Return a NEWLY-OWNED copy of the multiplier weight (a constant factor to
 * multiply with the eventual Ganak count). Caller must arjun_field_free(). */
arjun_field_t* arjun_simpcnf_get_multiplier_weight(const arjun_simpcnf_t* c);

/* ----------------------------------------------------------------- */
/* Arjun preprocessor                                                */
/* ----------------------------------------------------------------- */

arjun_arjun_t* arjun_new(void);
void           arjun_free(arjun_arjun_t* a);

void arjun_set_verb(arjun_arjun_t* a, uint32_t verb);
void arjun_set_seed(arjun_arjun_t* a, uint32_t seed);

/* Wrapper around Arjun::standalone_minimize_indep(cnf, all_indep). */
int arjun_standalone_minimize_indep(arjun_arjun_t* a,
                                    arjun_simpcnf_t* cnf,
                                    int all_indep);

/* Wrapper around Arjun::standalone_elim_to_file(cnf, etof_conf, simp_conf).
 * Default ElimToFileConf / SimpConf are used (etof.all_indep = 0). */
int arjun_standalone_elim_to_file(arjun_arjun_t* a, arjun_simpcnf_t* cnf);

#ifdef __cplusplus
}  /* extern "C" */
#endif

#endif /* ARJUN_C_H */
