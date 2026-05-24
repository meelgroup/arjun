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

#include "arjun_c.h"
#include "arjun_c_priv.hpp"

#include <gmpxx.h>

#include <string>
#include <vector>
#include <exception>

// Force default visibility on the C ABI symbols so they remain exported
// even when the library is compiled with -fvisibility=hidden.
#if defined _WIN32
    #define DLL_PUBLIC __declspec(dllexport)
#else
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
#endif

using namespace ArjunNS;

namespace {

// Thread-local error storage.
thread_local std::string g_last_error;

void set_error(const std::string& msg) { g_last_error = msg; }
void clear_error() { g_last_error.clear(); }

// Translate a DIMACS-style signed nonzero int into a CMSat::Lit.
// On success: writes *out and returns true. On failure: sets error and returns false.
bool dimacs_to_lit(int32_t lit_in, uint32_t nvars, CMSat::Lit* out) {
    if (lit_in == 0) { set_error("zero literal is not allowed"); return false; }
    uint32_t var = (uint32_t)(lit_in > 0 ? lit_in : -lit_in) - 1;
    if (var >= nvars) { set_error("literal references variable out of range"); return false; }
    *out = CMSat::Lit(var, lit_in < 0);  // sign=true means negated
    return true;
}

bool kinds_match(const arjun_field_t* a, const arjun_field_t* b) {
    return (a != nullptr) && (b != nullptr) && a->kind == b->kind;
}

}  // anonymous

extern "C" {

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

DLL_PUBLIC const char* arjun_last_error(void) { return g_last_error.c_str(); }

// ---------------------------------------------------------------------------
// FieldGen
// ---------------------------------------------------------------------------

DLL_PUBLIC arjun_fgen_t* arjun_fgen_mpz_new(void) {
    try {
        clear_error();
        auto* w = new arjun_fgen_t();
        w->fg = std::make_unique<FGenMpz>();
        w->kind = ARJUN_FIELD_MPZ;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_fgen_t* arjun_fgen_mpq_new(void) {
    try {
        clear_error();
        auto* w = new arjun_fgen_t();
        w->fg = std::make_unique<FGenMpq>();
        w->kind = ARJUN_FIELD_MPQ;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC void arjun_fgen_free(arjun_fgen_t* fg) { delete fg; }

DLL_PUBLIC arjun_field_kind arjun_fgen_kind(const arjun_fgen_t* fg) { return fg->kind; }

// ---------------------------------------------------------------------------
// Field
// ---------------------------------------------------------------------------

DLL_PUBLIC arjun_field_t* arjun_field_zero(const arjun_fgen_t* fg) {
    try {
        clear_error();
        auto* w = new arjun_field_t();
        w->f = fg->fg->zero();
        w->kind = fg->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_field_t* arjun_field_one(const arjun_fgen_t* fg) {
    try {
        clear_error();
        auto* w = new arjun_field_t();
        w->f = fg->fg->one();
        w->kind = fg->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_field_t* arjun_field_from_int(const arjun_fgen_t* fg, long val) {
    try {
        clear_error();
        auto* w = new arjun_field_t();
        if (fg->kind == ARJUN_FIELD_MPZ) {
            w->f = std::make_unique<FMpz>((int)val);
        } else {
            w->f = std::make_unique<FMpq>((int)val);
        }
        w->kind = fg->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_field_t* arjun_field_from_mpq(const arjun_fgen_t* fg, const mpq_t in) {
    try {
        clear_error();
        if (fg->kind != ARJUN_FIELD_MPQ) {
            set_error("arjun_field_from_mpq requires an MPQ field generator");
            return nullptr;
        }
        mpq_class v;
        mpq_set(v.get_mpq_t(), in);
        auto* w = new arjun_field_t();
        w->f = std::make_unique<FMpq>(v);
        w->kind = ARJUN_FIELD_MPQ;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_field_t* arjun_field_from_mpz(const arjun_fgen_t* fg, const mpz_t in) {
    try {
        clear_error();
        if (fg->kind != ARJUN_FIELD_MPZ) {
            set_error("arjun_field_from_mpz requires an MPZ field generator");
            return nullptr;
        }
        mpz_class v;
        mpz_set(v.get_mpz_t(), in);
        auto* w = new arjun_field_t();
        w->f = std::make_unique<FMpz>(v);
        w->kind = ARJUN_FIELD_MPZ;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC void arjun_field_free(arjun_field_t* f) { delete f; }

DLL_PUBLIC arjun_field_t* arjun_field_dup(const arjun_field_t* f) {
    try {
        clear_error();
        auto* w = new arjun_field_t();
        w->f = f->f->dup();
        w->kind = f->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC arjun_field_kind arjun_field_kind_of(const arjun_field_t* f) { return f->kind; }
DLL_PUBLIC int arjun_field_is_zero(const arjun_field_t* f) { return f->f->is_zero() ? 1 : 0; }
DLL_PUBLIC int arjun_field_is_one (const arjun_field_t* f) { return f->f->is_one()  ? 1 : 0; }

DLL_PUBLIC int arjun_field_get_mpz(const arjun_field_t* f, mpz_t out) {
    clear_error();
    if (f->kind != ARJUN_FIELD_MPZ) {
        set_error("arjun_field_get_mpz called on non-MPZ field"); return -1;
    }
    const auto& fz = static_cast<const FMpz&>(*f->f);
    mpz_set(out, fz.val.get_mpz_t());
    return 0;
}

DLL_PUBLIC int arjun_field_get_mpq(const arjun_field_t* f, mpq_t out) {
    clear_error();
    if (f->kind != ARJUN_FIELD_MPQ) {
        set_error("arjun_field_get_mpq called on non-MPQ field"); return -1;
    }
    const auto& fq = static_cast<const FMpq&>(*f->f);
    mpq_set(out, fq.val.get_mpq_t());
    return 0;
}

DLL_PUBLIC int arjun_field_mul_assign(arjun_field_t* a, const arjun_field_t* b) {
    clear_error();
    if (!kinds_match(a, b)) { set_error("kind mismatch"); return -1; }
    try { *a->f *= *b->f; return 0; }
    catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC int arjun_field_add_assign(arjun_field_t* a, const arjun_field_t* b) {
    clear_error();
    if (!kinds_match(a, b)) { set_error("kind mismatch"); return -1; }
    try { *a->f += *b->f; return 0; }
    catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC int arjun_field_sub_assign(arjun_field_t* a, const arjun_field_t* b) {
    clear_error();
    if (!kinds_match(a, b)) { set_error("kind mismatch"); return -1; }
    try { *a->f -= *b->f; return 0; }
    catch (const std::exception& e) { set_error(e.what()); return -1; }
}

// ---------------------------------------------------------------------------
// SimplifiedCNF
// ---------------------------------------------------------------------------

DLL_PUBLIC arjun_simpcnf_t* arjun_simpcnf_new(const arjun_fgen_t* fg) {
    try {
        clear_error();
        auto* w = new arjun_simpcnf_t();
        w->cnf  = new SimplifiedCNF(fg->fg);
        w->kind = fg->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC void arjun_simpcnf_free(arjun_simpcnf_t* c) {
    if (!c) return;
    delete c->cnf;
    delete c;
}

DLL_PUBLIC void arjun_simpcnf_new_vars(arjun_simpcnf_t* c, uint32_t n) { c->cnf->new_vars(n); }

DLL_PUBLIC uint32_t arjun_simpcnf_nvars(const arjun_simpcnf_t* c) { return c->cnf->nVars(); }

static int simpcnf_add_clause_impl(arjun_simpcnf_t* c,
                                   const int32_t* lits, size_t n_lits,
                                   bool redundant) {
    clear_error();
    try {
        std::vector<CMSat::Lit> cl;
        cl.reserve(n_lits);
        const uint32_t nv = c->cnf->nVars();
        for (size_t i = 0; i < n_lits; i++) {
            CMSat::Lit l;
            if (!dimacs_to_lit(lits[i], nv, &l)) return -1;
            cl.push_back(l);
        }
        if (redundant) c->cnf->add_red_clause(cl);
        else           c->cnf->add_clause(cl);
        return 0;
    } catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC int arjun_simpcnf_add_clause(arjun_simpcnf_t* c, const int32_t* lits, size_t n_lits) {
    return simpcnf_add_clause_impl(c, lits, n_lits, false);
}

DLL_PUBLIC int arjun_simpcnf_add_red_clause(arjun_simpcnf_t* c, const int32_t* lits, size_t n_lits) {
    return simpcnf_add_clause_impl(c, lits, n_lits, true);
}

DLL_PUBLIC void arjun_simpcnf_set_weighted(arjun_simpcnf_t* c, int weighted) {
    c->cnf->set_weighted(weighted != 0);
}

DLL_PUBLIC int arjun_simpcnf_get_weighted(const arjun_simpcnf_t* c) {
    return c->cnf->get_weighted() ? 1 : 0;
}

DLL_PUBLIC int arjun_simpcnf_set_lit_weight(arjun_simpcnf_t* c, int32_t lit,
                                 const arjun_field_t* weight) {
    clear_error();
    if (weight->kind != c->kind) { set_error("weight kind mismatch"); return -1; }
    CMSat::Lit l;
    if (!dimacs_to_lit(lit, c->cnf->nVars(), &l)) return -1;
    try {
        c->cnf->set_lit_weight(l, *weight->f);
        return 0;
    } catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC int arjun_simpcnf_set_sampl_vars(arjun_simpcnf_t* c,
                                 const uint32_t* vars, size_t n_vars) {
    clear_error();
    try {
        std::vector<uint32_t> v(vars, vars + n_vars);
        for (uint32_t x : v) {
            if (x >= c->cnf->nVars()) {
                set_error("sampling var out of range");
                return -1;
            }
        }
        c->cnf->set_sampl_vars(v);
        return 0;
    } catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC arjun_field_t* arjun_simpcnf_get_multiplier_weight(const arjun_simpcnf_t* c) {
    try {
        clear_error();
        auto* w = new arjun_field_t();
        w->f = c->cnf->get_multiplier_weight()->dup();
        w->kind = c->kind;
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

// ---------------------------------------------------------------------------
// Arjun
// ---------------------------------------------------------------------------

DLL_PUBLIC arjun_arjun_t* arjun_new(void) {
    try {
        clear_error();
        auto* w = new arjun_arjun_t();
        w->a = new Arjun();
        return w;
    } catch (const std::exception& e) { set_error(e.what()); return nullptr; }
}

DLL_PUBLIC void arjun_free(arjun_arjun_t* a) {
    if (!a) return;
    delete a->a;
    delete a;
}

DLL_PUBLIC void arjun_set_verb(arjun_arjun_t* a, uint32_t verb) { a->a->set_verb(verb); }
DLL_PUBLIC void arjun_set_seed(arjun_arjun_t* a, uint32_t seed) { a->a->set_seed(seed); }

DLL_PUBLIC int arjun_standalone_minimize_indep(arjun_arjun_t* a,
                                    arjun_simpcnf_t* cnf,
                                    int all_indep) {
    clear_error();
    try {
        a->a->standalone_minimize_indep(*cnf->cnf, all_indep != 0);
        return 0;
    } catch (const std::exception& e) { set_error(e.what()); return -1; }
}

DLL_PUBLIC int arjun_standalone_elim_to_file(arjun_arjun_t* a, arjun_simpcnf_t* cnf) {
    clear_error();
    try {
        Arjun::ElimToFileConf etof;
        SimpConf simp;
        a->a->standalone_elim_to_file(*cnf->cnf, etof, simp);
        return 0;
    } catch (const std::exception& e) { set_error(e.what()); return -1; }
}

}  // extern "C"
