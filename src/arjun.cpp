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
#include "config.h"
#include "common.h"
#include "GitSHA1.h"
#include <utility>
#include <tuple>
#include <limits>

using std::pair;
using std::numeric_limits;
using namespace ArjunInt;

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

DLL_PUBLIC bool Arjun::add_clause(const vector<CMSat::Lit>& lits)
{
    return arjdata->common.solver->add_clause(lits);
}

DLL_PUBLIC bool Arjun::add_xor_clause(const vector<uint32_t>& vars, bool rhs)
{
    assert(false && "Funnily enough this does NOT work. The XORs would generate a BVA variable, and that would then not be returned as part of the simplified CNF. We could calculate a smaller independent set, but that's all.");
    return arjdata->common.solver->add_xor_clause(vars, rhs);
}

DLL_PUBLIC bool Arjun::add_bnn_clause(
            const std::vector<CMSat::Lit>& lits,
            signed cutoff,
            Lit out
        )
{
    return arjdata->common.solver->add_bnn_clause(lits, cutoff, out);
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
    return ArjunIntNS::get_version_sha1();
}

DLL_PUBLIC std::string Arjun::get_solver_version_info()
{
    return arjdata->common.solver->get_text_version_info();
}

DLL_PUBLIC std::string Arjun::get_compilation_env()
{
    return arjdata->common.solver->get_compilation_env();
}

DLL_PUBLIC vector<uint32_t> Arjun::get_indep_set()
{
    double starTime = cpuTime();
    if (!arjdata->common.preproc_and_duplicate()) goto end;

    //Backward
    if (arjdata->common.conf.backward) {
        arjdata->common.backward_round();
    }

    end:
    arjdata->common.empty_out_indep_set_if_unsat();
    if (arjdata->common.conf.verb) {
        cout << "c [arjun] get_indep_set finished "
        << "T: " << std::setprecision(2) << std::fixed << (cpuTime() - starTime)
        << endl;
    }

    // Deal with empty_occs
    arjdata->common.sampling_set->insert(
        arjdata->common.sampling_set->begin(),
        arjdata->common.empty_occs.begin(),
        arjdata->common.empty_occs.end());

    return *arjdata->common.sampling_set;
}

DLL_PUBLIC const vector<CMSat::BNN*>& Arjun::get_bnns() const
{
    return arjdata->common.solver->get_bnns();
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
    if (arjdata->common.orig_num_vars == std::numeric_limits<uint32_t>::max()) {
        return arjdata->common.solver->nVars();
    }

    return arjdata->common.orig_num_vars;
}


DLL_PUBLIC void Arjun::set_verbosity(uint32_t verb)
{
    arjdata->common.conf.verb = verb;
    arjdata->common.solver->set_verbosity(verb);
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

DLL_PUBLIC void Arjun::set_pre_simplify(bool simp)
{
    arjdata->common.conf.pre_simplify = simp;
}

DLL_PUBLIC void Arjun::set_simp(bool simp)
{
    arjdata->common.conf.simp = simp;
}

DLL_PUBLIC void Arjun::set_incidence_sort(uint32_t incidence_sort)
{
    arjdata->common.conf.incidence_sort = incidence_sort;
}

DLL_PUBLIC void Arjun::set_or_gate_based(bool or_gate_based)
{
    arjdata->common.conf.or_gate_based = or_gate_based;
}

DLL_PUBLIC void Arjun::set_xor_gates_based(bool xor_gates_based)
{
    arjdata->common.conf.xor_gates_based = xor_gates_based;
}

DLL_PUBLIC void Arjun::set_probe_based(bool probe_based)
{
    arjdata->common.conf.probe_based = probe_based;
}

DLL_PUBLIC void Arjun::set_forward(bool forward)
{
    arjdata->common.conf.forward = forward;
}

DLL_PUBLIC void Arjun::set_backward(bool backward)
{
    //assert(backward && "We MUST have backward or we cannot work");
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

DLL_PUBLIC void Arjun::set_backbone_simpl_max_confl(uint64_t backbone_simpl_max_confl)
{
    arjdata->common.conf.backbone_simpl_max_confl = backbone_simpl_max_confl;
}

DLL_PUBLIC long unsigned Arjun::get_backbone_simpl_max_confl() const
{
    return arjdata->common.conf.backbone_simpl_max_confl;
}

DLL_PUBLIC uint32_t Arjun::get_verbosity() const
{
    return arjdata->common.conf.verb;
}

DLL_PUBLIC bool Arjun::get_fast_backw() const
{
    return arjdata->common.conf.fast_backw;
}

DLL_PUBLIC bool Arjun::get_distill() const
{
    return arjdata->common.conf.distill;
}

DLL_PUBLIC bool Arjun::get_intree() const
{
    return arjdata->common.conf.intree;
}

DLL_PUBLIC bool Arjun::get_guess() const
{
    return arjdata->common.conf.guess;
}

DLL_PUBLIC bool Arjun::get_pre_simplify() const
{
    return arjdata->common.conf.pre_simplify;
}

DLL_PUBLIC uint32_t Arjun::get_incidence_sort() const
{
    return arjdata->common.conf.incidence_sort;
}

DLL_PUBLIC bool Arjun::get_or_gate_based() const
{
    return arjdata->common.conf.or_gate_based;
}

DLL_PUBLIC bool Arjun::get_xor_gates_based() const
{
    return arjdata->common.conf.xor_gates_based;
}

DLL_PUBLIC bool Arjun::get_probe_based() const
{
    return arjdata->common.conf.probe_based;
}

DLL_PUBLIC bool Arjun::get_forward() const
{
    return arjdata->common.conf.forward;
}

DLL_PUBLIC bool Arjun::get_backward() const
{
    return arjdata->common.conf.backward;
}

DLL_PUBLIC bool Arjun::get_assign_fwd_val() const
{
    return arjdata->common.conf.assign_fwd_val;
}

DLL_PUBLIC uint32_t Arjun::get_backw_max_confl() const
{
    return arjdata->common.conf.backw_max_confl;
}

DLL_PUBLIC void Arjun::set_gauss_jordan(bool gauss_jordan)
{
    arjdata->common.conf.gauss_jordan = gauss_jordan;
}

DLL_PUBLIC bool Arjun::get_gauss_jordan() const
{
    return arjdata->common.conf.gauss_jordan;
}

DLL_PUBLIC void Arjun::set_regularly_simplify(bool reg_simp)
{
    arjdata->common.conf.regularly_simplify = reg_simp;
}

DLL_PUBLIC bool Arjun::get_regularly_simplify() const
{
    return arjdata->common.conf.regularly_simplify;
}

DLL_PUBLIC void Arjun::set_fwd_group(uint32_t forward_group)
{
    arjdata->common.conf.forward_group = forward_group;
}

DLL_PUBLIC uint32_t Arjun::get_fwd_group() const
{
    return arjdata->common.conf.forward_group;
}

DLL_PUBLIC void Arjun::set_ite_gate_based(bool ite_gate_based)
{
    arjdata->common.conf.ite_gate_based = ite_gate_based;
}

DLL_PUBLIC bool Arjun::get_ite_gate_based() const
{
    return arjdata->common.conf.ite_gate_based;
}

DLL_PUBLIC void Arjun::set_irreg_gate_based(const bool irreg_gate_based)
{
    arjdata->common.conf.irreg_gate_based = irreg_gate_based;
}

DLL_PUBLIC bool Arjun::get_irreg_gate_based() const
{
    return arjdata->common.conf.irreg_gate_based;
}

DLL_PUBLIC vector<Lit> Arjun::get_zero_assigned_lits() const
{
    vector<Lit> ret;
    vector<Lit> lits = arjdata->common.solver->get_zero_assigned_lits();
    for(const auto& lit: lits) {
        if (lit.var() < arjdata->common.orig_num_vars) {
            ret.push_back(lit);
        }
    }

    return ret;
}

DLL_PUBLIC std::vector<std::pair<CMSat::Lit, CMSat::Lit> > Arjun::get_all_binary_xors() const
{
    vector<pair<Lit, Lit>> ret;
    const auto bin_xors = arjdata->common.solver->get_all_binary_xors();
    for(const auto& bx: bin_xors) {
        if (bx.first.var() < arjdata->common.orig_num_vars &&
            bx.second.var() < arjdata->common.orig_num_vars)
        {
            ret.push_back(bx);
        }
    }

    return ret;
}

DLL_PUBLIC void Arjun::set_backbone_simpl(bool backbone_simpl)
{
    arjdata->common.conf.backbone_simpl = backbone_simpl;
}

DLL_PUBLIC bool Arjun::get_backbone_simpl() const
{
    return arjdata->common.conf.backbone_simpl;
}

DLL_PUBLIC void Arjun::varreplace()
{
    //arjdata->common.solver->backbone_simpl();
    std::string tmp("must-scc-vrepl, cl-consolidate");
    arjdata->common.solver->simplify(NULL, &tmp);
}

DLL_PUBLIC vector<uint32_t> Arjun::get_empty_occ_sampl_vars() const
{
    return arjdata->common.empty_occs;
}

DLL_PUBLIC const vector<Lit> Arjun::get_internal_cnf(uint32_t& num_cls) const
{
    vector<Lit> cnf;
    bool ret = true;
    num_cls = 0;

    arjdata->common.solver->start_getting_small_clauses(
        std::numeric_limits<uint32_t>::max(),
        std::numeric_limits<uint32_t>::max(),
        false);
    vector<Lit> clause;
    while (ret) {
        ret = arjdata->common.solver->get_next_small_clause(clause);
        if (!ret) break;

        bool ok = true;
        for(auto l: clause) {
            if (l.var() >= arjdata->common.orig_num_vars) {
                ok = false;
                break;
            }
        }

        if (ok) {
            for(auto const& l: clause) cnf.push_back(l);
            cnf.push_back(lit_Undef);
            num_cls++;
        }
    }
    arjdata->common.solver->end_getting_small_clauses();
    return cnf;
}

static std::pair<vector<vector<Lit>>, uint32_t> get_simplified_renumbered_cnf(SATSolver* solver, vector<uint32_t>& sampl_vars)
{
    vector<vector<Lit>> cnf;
    solver->start_getting_small_clauses(
        std::numeric_limits<uint32_t>::max(),
        std::numeric_limits<uint32_t>::max(),
        false, //red
        false, //bva vars
        true); //simplified

    sampl_vars = solver->translate_sampl_set(sampl_vars);

    bool ret = true;
    vector<Lit> clause;
    while(ret) {
        ret = solver->get_next_small_clause(clause);
        if (ret) {
            cnf.push_back(clause);
        }
    }
    solver->end_getting_small_clauses();
    return std::make_pair(cnf, solver->simplified_nvars());
}

static vector<Lit> fill_solver_no_empty(
    const vector<uint32_t>& sampl_vars,
    const vector<uint32_t>& empty_vars,
    const uint32_t orig_num_vars,
    SATSolver& solver, // Solver here is EMPTY
    Arjun* arjun)
{
    // We create a new Solver that has all variables (except empty)
    solver.new_vars(orig_num_vars-empty_vars.size());
    vector<char> seen(orig_num_vars, 0);
    vector<uint32_t> mymap;
    for(auto const& e: empty_vars) {
        assert(e < orig_num_vars);
        seen[e] = 1;
    }

    uint32_t at = 0;
    for(uint32_t i = 0; i < orig_num_vars; i++) {
        if (!seen[i]) {
            mymap.push_back(at);
            at++;
        } else {
            mymap.push_back(numeric_limits<uint32_t>::max());
        }
    }
    assert(at == solver.nVars());

    //NOTE: we can have binary XORs that refer to EMPTY. This is because
    //      var x (in sampling set) was replaced by var y, which became empty.
    vector<Lit> tmp;
    uint32_t sz = 0;
    bool ok = true;
    uint32_t num_cls;
    const auto cnf = arjun->get_internal_cnf(num_cls);
    for(const auto& l: cnf) {
        if (l != lit_Undef) {
            if (seen[l.var()] == 1) ok = false;
            if (ok) tmp.push_back(Lit(mymap[l.var()], l.sign()));
            sz++;
            continue;
        }
        if (ok) solver.add_clause(tmp);
        else assert(sz == 2);
        tmp.clear();
        ok = true;
        sz = 0;
    }

    arjun->varreplace();

    auto bin_xors = arjun->get_all_binary_xors();
    vector<uint32_t> dummy_v;
    for(const auto& bx: bin_xors) {
        dummy_v.clear();
        if (seen[bx.first.var()] == 0 && seen[bx.second.var()] == 0) { // see note above
            dummy_v.push_back(mymap[bx.first.var()]);
            dummy_v.push_back(mymap[bx.second.var()]);
            solver.add_xor_clause(dummy_v, bx.first.sign()^bx.second.sign());
        }
    }

    vector<Lit> dont_elim;
    set<Lit> dont_elim_set;
    for(const auto& v: sampl_vars) {
        if (seen[v]) continue;
        dont_elim_set.insert(Lit(mymap[v], false));
    }
    for(const auto& l: dont_elim_set) dont_elim.push_back(l);

    return dont_elim;
}

DLL_PUBLIC std::tuple<pair<vector<vector<Lit>>, uint32_t>, vector<uint32_t>, uint32_t>
Arjun::get_fully_simplified_renumbered_cnf(
    const vector<uint32_t>& sampl_vars, //contains empty_vars!
    const vector<uint32_t>& empty_vars,
    const uint32_t orig_num_vars,
    const bool sparsify,
    const bool renumber)
{
    CMSat::SATSolver solver;
    solver.set_verbosity(arjdata->common.conf.verb);
    solver.set_renumber(renumber);
    solver.set_scc(renumber);
    auto dont_elim = fill_solver_no_empty(
        sampl_vars, empty_vars, orig_num_vars, solver, this);

    //Below works VERY WELL for: ProcessBean, pollard, track1_116.mcc2020_cnf
    //   and blasted_TR_b14_even3_linear.cnf.gz.no_w.cnf
    //with CMS ef6ea7e87e00bde50c0cce0c1e13a012191c4e1c and Arjun 5f2dfe814e07ee6ee0dde65b1350b5c343209ed0
    solver.set_min_bva_gain(0);
    solver.set_varelim_check_resolvent_subs(true);
    solver.set_max_red_linkin_size(0);
    solver.set_timeout_all_calls(100);
    solver.set_weaken_time_limitM(2000);
    solver.set_occ_based_lit_rem_time_limitM(500);


    // occ-ternary-res not used
    // eqlit-find ? (too slow)
    string str("full-probe, sub-cls-with-bin, must-scc-vrepl, must-scc-vrepl, distill-cls-onlyrem, sub-impl, occ-resolv-subs, occ-del-blocked, occ-backw-sub, occ-rem-with-orgates, occ-bve, occ-ternary-res, ");
    solver.simplify(&dont_elim, &str);
    str = string(",intree-probe, occ-backw-sub-str, sub-str-cls-with-bin, clean-cls, distill-cls,distill-bins, ") + str;

    solver.simplify(&dont_elim, &str);
    solver.simplify(&dont_elim, &str);
    solver.simplify(&dont_elim, &str);
    if (sparsify) {
        str = string("sparsify,") + str;
        solver.simplify(&dont_elim, &str);
    }

    str = string("");
    if (arjdata->common.definitely_satisfiable) {
        str += string("occ-rem-unconn-assumps, ");
    }
    str += string(", must-scc-vrepl, must-renumber");
    solver.simplify(&dont_elim, &str);

    vector<uint32_t> new_sampl_set;
    for(const auto& l: dont_elim) new_sampl_set.push_back(l.var());
    auto cnf = get_simplified_renumbered_cnf(&solver, new_sampl_set);
    return std::make_tuple(cnf, new_sampl_set, empty_vars.size());
}


DLL_PUBLIC void Arjun::set_pred_forever_cutoff(int pred_forever_cutoff)
{
    arjdata->common.solver->set_pred_forever_cutoff(pred_forever_cutoff);
}

DLL_PUBLIC void Arjun::set_every_pred_reduce(int every_pred_reduce)
{
    arjdata->common.solver->set_every_pred_reduce(every_pred_reduce);
}

DLL_PUBLIC void Arjun::set_empty_occs_based(const bool empty_occs_based)
{
    arjdata->common.conf.empty_occs_based = empty_occs_based;
}

DLL_PUBLIC void Arjun::set_mirror_empty(const bool mirror_empty)
{
    arjdata->common.conf.mirror_empty = mirror_empty;
}
