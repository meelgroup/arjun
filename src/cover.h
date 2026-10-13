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


#pragma once

#include "arjun.h"
#include "config.h"
#include "metasolver.h"
#include "aig_to_cnf.h"
#include <map>
#include <set>
#include <unordered_map>

namespace ArjunInt {

// An AIG with its leaves replaced: a var with a `leaf` by that, any other
// defined var by its def, rewritten the same way, the rest by their `val`.
// What does not depend on a `val` is built once, the rest once per round.
struct Subst {
    struct Res { ArjunNS::aig_lit a; bool fixed; };
    struct NidHash { size_t operator()(const ArjunNS::AIG* n) const { return std::hash<uint64_t>()(n->nid); } };
    const ArjunNS::SimplifiedCNF& cnf;
    std::vector<ArjunNS::aig_lit> leaf;
    std::vector<CMSat::lbool> val;
    std::unordered_map<const ArjunNS::AIG*, Res, NidHash> fixed_nodes, round_nodes;
    std::vector<Res> var_res;
    std::vector<uint64_t> var_round;
    uint64_t round = 1, work = 0;

    explicit Subst(const ArjunNS::SimplifiedCNF& _cnf) : cnf(_cnf), leaf(_cnf.num_defs(), ArjunNS::aig_lit(nullptr)),
        val(_cnf.num_defs(), CMSat::l_Undef), var_res(_cnf.num_defs()), var_round(_cnf.num_defs(), 0) {}

    void new_round() { round_nodes.clear(); round++; }

    Res of_var(const uint32_t v) {
        if (leaf[v] != nullptr) return {leaf[v], true};
        if (!cnf.defined(v)) {
            assert(val[v] != CMSat::l_Undef);
            return {ArjunNS::AIG::new_const(val[v] == CMSat::l_True), false};
        }
        if (var_round[v] == round || var_round[v] == 1) return var_res[v];
        const Res ret = of_aig(cnf.get_def(v));
        var_res[v] = ret;
        var_round[v] = ret.fixed ? 1 : round;
        return ret;
    }

    Res of_aig(const ArjunNS::aig_lit& a) {
        const ArjunNS::AIG* n = a.get();
        Res ret;
        if (n->type == ArjunNS::AIGT::t_const) ret = {ArjunNS::aig_lit(a.node, false), true};
        else if (n->type == ArjunNS::AIGT::t_lit) ret = of_var(n->var);
        else {
            const Res* found = nullptr;
            if (auto it = fixed_nodes.find(n); it != fixed_nodes.end()) found = &it->second;
            else if (auto it2 = round_nodes.find(n); it2 != round_nodes.end()) found = &it2->second;
            if (found) ret = *found;
            else {
                work++;
                const Res l = of_aig(n->l), r = of_aig(n->r);
                ret = {ArjunNS::AIG::new_and(l.a, r.a), l.fixed && r.fixed};
                (ret.fixed ? fixed_nodes : round_nodes)[n] = ret;
            }
        }
        return {a.neg ? ~ret.a : ret.a, ret.fixed};
    }
};

// The covering of clauses that share existentials. abs picks an X no model
// settles yet, f gives a model of the clauses for it
class CoverComp {
public:
    CoverComp(const ArjunNS::SimplifiedCNF& _cnf, const std::vector<std::vector<CMSat::Lit>>& _cls, const ArjunNS::Arjun::CoverConf& _mconf,
            const uint64_t _max_ticks, const uint32_t _verb) :
        cnf(_cnf), cls(_cls), mconf(_mconf), max_ticks(_max_ticks), verb(_verb),
        orig_sampl_vars(_cnf.get_orig_sampl_vars()), aig_mng(_cnf.get_aig_mng()), num_defs(_cnf.num_defs()),
        sat_minim(_mconf.minim & 1), flip_minim(_mconf.minim & 2), subs_minim(_mconf.minim & 4),
        in_f_vars(_cnf), in_abs_vars(_cnf), in_orig_vars(_cnf), enc_f(f), enc_abs(abs) {}

    // new_defs: the functions found are added, for the caller to set
    CMSat::lbool run(std::vector<CMSat::lbool>& cex, std::vector<std::pair<uint32_t, ArjunNS::aig_lit>>& new_defs);
    uint64_t ticks() { return abs.get_sum_ticks() + f.get_sum_ticks() + in_abs_vars.work * 10; }

private:
    void add_vars_and_cls();
    void tie_defs();
    void add_helpers();
    void find_subsumed();
    void add_selectors();
    void set_phases();
    void init_flip();

    bool outer_only_cex(std::vector<CMSat::lbool>& cex);
    void set_cex(std::vector<CMSat::lbool>& cex);
    void skip_cube();
    void add_cls_to_abs();
    void refine();
    void get_some_false(const std::vector<CMSat::lbool>& model);
    bool flip(std::vector<CMSat::lbool>& model);
    std::vector<CMSat::lbool> minimize(std::vector<CMSat::lbool> model);
    void drop_subsumed(std::vector<CMSat::Lit>& hs);
    ArjunNS::aig_lit deep_true(Subst& s);
    void build_funs(std::vector<std::pair<uint32_t, ArjunNS::aig_lit>>& new_defs);

    bool out_of_ticks() { return max_ticks != 0 && ticks() >= max_ticks; }
    CMSat::Lit in_f(const CMSat::Lit l) const { return CMSat::Lit(to_f[l.var()], l.sign()); }
    uint32_t hidx(const CMSat::Lit h) const { return h.var() - helper_at; }
    CMSat::Lit sel(const uint32_t i) const { return CMSat::Lit(sel_at + i, false); }
    void new_f_var(const uint32_t v) {
        to_f[v] = f.nVars();
        f.new_var();
    }
    void print_stats(const char* what);
    CMSat::lbool finish(const CMSat::lbool ret);

    const ArjunNS::SimplifiedCNF& cnf;
    const std::vector<std::vector<CMSat::Lit>>& cls;
    const ArjunNS::Arjun::CoverConf& mconf;
    const uint64_t max_ticks;
    const uint32_t verb;
    const std::set<uint32_t>& orig_sampl_vars;
    const ArjunNS::AIGManager& aig_mng;
    const uint32_t num_defs;
    const bool sat_minim, flip_minim, subs_minim;
    MetaSolver abs, f;

    // The vars that already have a function. One of the universals only is
    // an outer var like them: abs picks it, tied to its function there. Any
    // other one follows the existentials: `deep`, the clauses they are in,
    // are rewritten for every model.
    std::vector<char> state;
    std::vector<uint32_t> defined, free_leaves;
    std::vector<uint32_t> outer;
    uint32_t num_univ = 0;
    std::vector<char> is_outer;

    // The solvers only get the vars they have clauses on: the outer ones,
    // at the same index in both, then for f the rest
    std::vector<uint32_t> to_f, ys;

    Subst in_f_vars, in_abs_vars, in_orig_vars;
    std::vector<ArjunNS::aig_lit> keep; // the encoders cache by node address
    ArjunNS::AIGToCNF<MetaSolver> enc_f, enc_abs;

    // per clause with outer vars: its existentials, and a helper that
    // implies all of its outer literals are false
    uint32_t helper_at = 0, num_helpers = 0;
    std::map<std::vector<CMSat::Lit>, CMSat::Lit> univ_to_helper;
    std::vector<std::pair<std::vector<CMSat::Lit>, CMSat::Lit>> mixed;
    std::vector<ArjunNS::aig_lit> univ_true; // per helper: some outer literal of it is true
    std::vector<std::vector<CMSat::Lit>> deep, outer_only;

    // subs[b]: the helpers whose outer literals are a subset of b's. With one
    // of them in a refinement, b says nothing more
    std::vector<std::vector<uint32_t>> subs;
    std::vector<char> present;
    std::vector<CMSat::Lit> kept;

    // selector of a helper, in f: the existentials satisfy all of its clauses
    uint32_t sel_at = 0;
    std::vector<uint32_t> wait, skip;
    std::vector<char> is_false, in_core;

    // An existential is flipped if no clause needs its value, at this X, and
    // the other one satisfies more existential parts. No SAT call
    std::vector<std::vector<CMSat::Lit>> flip_cls;
    std::vector<char> flip_mixed, can_flip;
    std::vector<std::vector<uint32_t>> flip_occ;
    std::vector<uint32_t> flip_vars, num_true, num_true_ex;

    // per refinement, for the Skolem functions: its helpers, and the model's Y
    std::vector<std::vector<CMSat::Lit>> ref_helpers;
    std::vector<bool> ref_ys;

    std::vector<CMSat::Lit> assumps, some_false;
    double cost = 0;
    uint64_t rounds = 0, ref_lits = 0, cubes = 0, cube_lits = 0, minim_calls = 0, minim_removed = 0;
    uint64_t subsumed = 0, flips = 0;
    double start_time = 0, setup_time = 0;
    double abs_time = 0, f_time = 0, refine_time = 0, deep_time = 0, funs_time = 0;
};

// Covers the X space with models of `cls`, over ORIG vars: a model settles
// every X that satisfies the universal parts of the clauses its Y leaves
// unsatisfied. This is the CEGAR of the 2QBF literature. l_True: the
// vars with no def yet got their Skolem functions, l_Undef: gave up. An X
// with no Y is returned in `cex` with l_False if stop_at_cex, else its
// cube is skipped, and abs gets cls so that no more of them come up.
// The limits and the ways a refinement is shortened: see Arjun::CoverConf.
//
// The defs that cnf already has are kept, and used: a model is then the
// values of the vars with no def, and it settles the X for which the
// clauses hold with the defined vars following their defs.
class Cover {
public:
    Cover(const Config& _conf, const ArjunNS::Arjun::CoverConf& _mconf, ArjunNS::SimplifiedCNF& _cnf,
            const std::vector<std::vector<CMSat::Lit>>& _cls) :
        conf(_conf), mconf(_mconf), cnf(_cnf), cls(_cls) {}
    CMSat::lbool run(std::vector<CMSat::lbool>& cex);

private:
    void split_components();
    CMSat::lbool cover_components(std::vector<CMSat::lbool>& cex);
    CMSat::lbool cover_one(const std::vector<std::vector<CMSat::Lit>>& comp_cls, const uint32_t verb,
            std::vector<CMSat::lbool>& cex);
    void set_funs();

    const Config& conf;
    const ArjunNS::Arjun::CoverConf& mconf;
    ArjunNS::SimplifiedCNF& cnf;
    const std::vector<std::vector<CMSat::Lit>>& cls;

    std::vector<std::vector<std::vector<CMSat::Lit>>> comps;
    std::vector<std::vector<CMSat::Lit>> outer_only;
    std::vector<std::pair<uint32_t, ArjunNS::aig_lit>> new_defs;
    uint64_t used_ticks = 0;
};

}
