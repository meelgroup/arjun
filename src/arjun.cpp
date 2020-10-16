/*
 Arjun

 Copyright (c) 2020, Mate Soos and Kuldeep S. Meel. All rights reserved.

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
 */

#include "arjun.h"
#include <cryptominisat5/cryptominisat.h>
#include "cryptominisat5/dimacsparser.h"
#include "cryptominisat5/streambuffer.h"
#include "config.h"
#include "common.h"
#include "GitSHA1.h"

#if defined _WIN32
    #define DLL_PUBLIC __declspec(dllexport)
#else
    #define DLL_PUBLIC __attribute__ ((visibility ("default")))
    #define DLL_LOCAL  __attribute__ ((visibility ("hidden")))
#endif

namespace ArjunNS {
    struct ArjPrivateData {
        Common common;
    };
}

using namespace ArjunNS;


DLL_PUBLIC Arjun::Arjun()
{
    arjdata = new ArjPrivateData;
}

DLL_PUBLIC Arjun::~Arjun()
{
    delete arjdata;
}

// DLL_PUBLIC void Arjun::set_projection_set(const vector<uint32_t>& vars)
// {
//     //arjdata->conf.sampling_set = vars;
//     assert(false);
// }


DLL_PUBLIC uint32_t Arjun::nVars() {
    return arjdata->common.solver->nVars();
}

DLL_PUBLIC void Arjun::new_vars(uint32_t num)
{
    arjdata->common.solver->new_vars(num);
}

DLL_PUBLIC void Arjun::new_var()
{
    arjdata->common.solver->new_var();
}

DLL_PUBLIC void Arjun::add_clause(const vector<CMSat::Lit>& lits)
{
    arjdata->common.solver->add_clause(lits);
}

DLL_PUBLIC void Arjun::add_xor_clause(const vector<uint32_t>& vars, bool rhs)
{
    arjdata->common.solver->add_xor_clause(vars, rhs);
}

DLL_PUBLIC uint32_t Arjun::set_starting_sampling_set(const vector<uint32_t>& vars)
{
    *arjdata->common.sampling_set = vars;
    return arjdata->common.sampling_set->size();
}

DLL_PUBLIC uint32_t Arjun::start_with_clean_sampling_set()
{
    arjdata->common.start_with_clean_sampling_set();
    return arjdata->common.sampling_set->size();
}

DLL_PUBLIC string Arjun::get_version_info()
{
    return get_version_sha1();
}

DLL_PUBLIC std::string Arjun::get_solver_version_info()
{
    return arjdata->common.solver->get_version();
}

DLL_PUBLIC vector<uint32_t> Arjun::get_indep_set()
{
    double starTime = cpuTime();
    arjdata->common.preproc_and_duplicate();

    if (arjdata->common.conf.guess) {
        arjdata->common.run_guess();
    }

    if (arjdata->common.conf.forward) {
        if (arjdata->common.conf.verb) {
            cout << "c [mis] FORWARD " << endl;
        }
        uint32_t guess_indep = std::max<uint32_t>(arjdata->common.sampling_set->size()/100, 10);
        arjdata->common.forward_round(50000, guess_indep, 0);
    }

    if (arjdata->common.conf.backward) {
        if (arjdata->common.conf.verb) {
            cout << "c [mis] BACKWARD " << endl;
        }
        arjdata->common.backward_round();
    }

    if (arjdata->common.conf.verb) {
        cout << "c [mis] "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
        << endl;
    }

    return *arjdata->common.sampling_set;
}

DLL_PUBLIC void Arjun::start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red)
{
    arjdata->common.solver->start_getting_small_clauses(max_len, max_glue, red);
}

DLL_PUBLIC bool Arjun::get_next_small_clause(std::vector<CMSat::Lit>& ret)
{
    return arjdata->common.solver->get_next_small_clause(ret);
}

DLL_PUBLIC void Arjun::end_getting_small_clauses()
{
    arjdata->common.solver->end_getting_small_clauses();
}

DLL_PUBLIC uint32_t Arjun::get_orig_num_vars() const
{
    return arjdata->common.orig_num_vars;
}


DLL_PUBLIC void Arjun::set_verbosity(uint32_t verb)
{
    arjdata->common.conf.verb = verb;
}

DLL_PUBLIC void Arjun::set_seed(uint32_t seed)
{
    arjdata->common.random_source.seed(seed);
}


DLL_PUBLIC void Arjun::set_fast_backw(bool fast_backw)
{
    arjdata->common.conf.fast_backw = fast_backw;
}

DLL_PUBLIC void Arjun::set_distill(bool distill)
{
    arjdata->common.conf.distill = distill;
}

DLL_PUBLIC void Arjun::set_intree(bool intree)
{
    arjdata->common.conf.intree = intree;
}

DLL_PUBLIC void Arjun::set_guess(bool guess)
{
    arjdata->common.conf.guess = guess;
}

DLL_PUBLIC void Arjun::set_simp(bool simp)
{
    arjdata->common.conf.simp = simp;
}

DLL_PUBLIC void Arjun::set_incidence_sort(uint32_t incidence_sort)
{
    arjdata->common.conf.incidence_sort = incidence_sort;
}

DLL_PUBLIC void Arjun::set_gate_based(bool gate_based)
{
    arjdata->common.conf.gate_based = gate_based;
}

DLL_PUBLIC void Arjun::set_xor_based(bool xor_based)
{
    arjdata->common.conf.xor_based = xor_based;
}

DLL_PUBLIC void Arjun::set_probe_based(bool probe_based)
{
    arjdata->common.conf.probe_based = probe_based;
}

DLL_PUBLIC void Arjun::set_polarmode(bool polarmode)
{
    arjdata->common.conf.polarmode = polarmode;
}

DLL_PUBLIC void Arjun::set_forward(bool forward)
{
    arjdata->common.conf.forward = forward;
}

DLL_PUBLIC void Arjun::set_backward(bool backward)
{
    assert(backward && "We MUST have backward or we cannot work");
    arjdata->common.conf.backward = backward;
}

DLL_PUBLIC void Arjun::set_assign_fwd_val(bool assign_fwd_val)
{
    arjdata->common.conf.assign_fwd_val = assign_fwd_val;
}

DLL_PUBLIC void Arjun::set_backw_max_confl(uint32_t backw_max_confl)
{
    arjdata->common.conf.backw_max_confl = backw_max_confl;
}


DLL_PUBLIC uint32_t Arjun::get_verbosity()
{
    return arjdata->common.conf.verb;
}

DLL_PUBLIC bool Arjun::get_fast_backw()
{
    return arjdata->common.conf.fast_backw;
}

DLL_PUBLIC bool Arjun::get_distill()
{
    return arjdata->common.conf.distill;
}

DLL_PUBLIC bool Arjun::get_intree()
{
    return arjdata->common.conf.intree;
}

DLL_PUBLIC bool Arjun::get_guess()
{
    return arjdata->common.conf.guess;
}

DLL_PUBLIC bool Arjun::get_simp()
{
    return arjdata->common.conf.simp;
}

DLL_PUBLIC uint32_t Arjun::get_incidence_sort()
{
    return arjdata->common.conf.incidence_sort;
}

DLL_PUBLIC bool Arjun::get_gate_based()
{
    return arjdata->common.conf.gate_based;
}

DLL_PUBLIC bool Arjun::get_xor_based()
{
    return arjdata->common.conf.xor_based;
}

DLL_PUBLIC bool Arjun::get_probe_based()
{
    return arjdata->common.conf.probe_based;
}

DLL_PUBLIC bool Arjun::get_polarmode()
{
    return arjdata->common.conf.polarmode;
}

DLL_PUBLIC bool Arjun::get_forward()
{
    return arjdata->common.conf.forward;
}

DLL_PUBLIC bool Arjun::get_backward()
{
    return arjdata->common.conf.backward;
}

DLL_PUBLIC bool Arjun::get_assign_fwd_val()
{
    return arjdata->common.conf.assign_fwd_val;
}

DLL_PUBLIC uint32_t Arjun::get_backw_max_confl()
{
    return arjdata->common.conf.backw_max_confl;
}
