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
#include "cover_problem.h"
#include "time_mem.h"
#include <limits>
#include <map>
#include <set>
#include <functional>
#include <unordered_map>

namespace ArjunInt {

struct UnionFind {
    std::vector<uint32_t> par;
    explicit UnionFind(const uint32_t n) : par(n) { for (uint32_t v = 0; v < n; v++) par[v] = v; }
    uint32_t find(uint32_t v) {
        while (par[v] != v) v = par[v] = par[par[v]];
        return v;
    }
    void join(const uint32_t a, const uint32_t b) { par[find(a)] = find(b); }
};

// An AIG with its leaves replaced: a var with a `leaf` by that, any other
// defined var by its def, rewritten the same way, the rest by their `val`.
// What does not depend on a `val` is built once, the rest once per round.
struct Subst {
    struct Res { ArjunNS::aig_lit a; bool fixed; };
    struct NidHash { size_t operator()(const ArjunNS::AIG* n) const { return std::hash<uint64_t>()(n->nid); } };
    const CoverProblem& problem;
    std::vector<ArjunNS::aig_lit> leaf;
    std::vector<CMSat::lbool> val;
    std::unordered_map<const ArjunNS::AIG*, Res, NidHash> fixed_nodes, round_nodes;
    std::vector<Res> var_res;
    std::vector<uint64_t> var_round;
    uint64_t round = 1, work = 0;

    explicit Subst(const CoverProblem& _problem) : problem(_problem), leaf(_problem.size(), ArjunNS::aig_lit(nullptr)),
        val(_problem.size(), CMSat::l_Undef), var_res(_problem.size()), var_round(_problem.size(), 0) {}

    void new_round() { round_nodes.clear(); round++; }

    Res of_var(const uint32_t v) {
        if (leaf[v] != nullptr) return {leaf[v], true};
        if (!problem.defined(v)) {
            assert(val[v] != CMSat::l_Undef);
            return {ArjunNS::AIG::new_const(val[v] == CMSat::l_True), false};
        }
        if (var_round[v] == round || var_round[v] == 1) return var_res[v];
        const Res ret = of_aig(problem.def[v]);
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

// The x part of a clause with ys gets a helper var in x_solver, true: all
// of the x part is false. Clauses with the same x part share it
struct Helper {
    std::vector<CMSat::Lit> x_part; // sorted, over `problem`
    CMSat::Lit lit;
    ArjunNS::aig_lit x_part_true;
};
struct SplitClause {
    std::vector<CMSat::Lit> y_part; // in y_solver
    uint32_t helper;
};

// A model for the same X whose ys satisfy the y parts that the given one
// does, and as many more as the cores allow: a selector per helper in
// y_solver, true: all of its clauses' y parts hold. A helper in a core
// waits longer and longer before it is tried again
class RefinementMinimizer {
public:
    RefinementMinimizer() = default;
    // adds the selectors and their clauses to y_solver
    RefinementMinimizer(MetaSolver& y_solver, const std::vector<SplitClause>& split_cls, uint32_t num_helpers,
            const ArjunNS::Arjun::CoverConf& cconf);
    // assumps: the X; false_helpers: the indices of the helpers whose y parts `model` leaves false
    std::vector<CMSat::lbool> minimize(std::vector<CMSat::lbool> model, std::vector<CMSat::Lit>& assumps,
            const std::vector<uint32_t>& false_helpers, const std::function<CMSat::lbool(std::vector<CMSat::Lit>&)>& solve,
            const std::function<bool()>& out_of_ticks);
    uint64_t calls = 0;

private:
    CMSat::Lit selector(const uint32_t i) const { return CMSat::Lit(sel_base + i, false); }
    MetaSolver* y_solver = nullptr;
    uint32_t sel_base = 0, max_calls = 0, max_wait = 0;
    std::vector<uint32_t> backoff, skip_rounds;
    std::vector<char> is_false_helper, in_core;
};

// The covering of clauses that share ys. x_solver picks an X no model
// settles yet, y_solver gives a model of the clauses for it
class CoverComponent {
public:
    struct Conf : ArjunNS::Arjun::CoverConf {
        // counting: the clauses of X only restrict X, an X that falsifies them is no cex
        bool assume_outer = false;
        // What an X with no Y does. stop: it is returned as the cex. skip: its
        // cube is blocked, and x_solver gets the clauses so that no more come
        // up. keep: its cube is blocked and kept, l_True comes with all of them,
        // more than max_cubes gives up; x_solver never gets the clauses
        enum class NoY { stop, skip, keep };
        NoY no_y = NoY::skip;
        uint32_t max_cubes = 0;
        bool minim_cubes = true; // drop the literals of a kept cube that it does not need
    };
    CoverComponent(const CoverProblem& _problem, const ArjunNS::AIGManager& _aig_mng, const std::vector<std::vector<CMSat::Lit>>& _comp_cls,
            const Conf& _cconf, const uint64_t _max_ticks, const uint32_t _verb) :
        problem(_problem), aig_mng(_aig_mng), comp_cls(_comp_cls), cconf(_cconf), max_ticks(_max_ticks), verb(_verb),
        num_vars(_problem.size()), sat_minim(_cconf.sat_minim),
        defs_in_y(_problem), defs_in_x(_problem), defs_in_vars(_problem), enc_y(y_solver), enc_x(x_solver) {}

    using Funs = std::vector<std::pair<uint32_t, ArjunNS::aig_lit>>;
    struct Result {
        CMSat::lbool ret = CMSat::l_Undef;
        std::vector<CMSat::lbool> cex; // l_False: an X with no Y
        Funs funs; // l_True and need_funs: the functions found, for the caller to set
        // l_True with no X-cube blocked and no function of X: the clauses say nothing of X
        bool every_x_has_y = false;
    };
    Result cegar_run();
    uint64_t ticks() { return x_solver.get_sum_ticks() + y_solver.get_sum_ticks() + defs_in_x.work * 10; }
    uint64_t conflicts() const { return x_solver.get_sum_conflicts() + y_solver.get_sum_conflicts(); }
    bool out_of_ticks() { return gave_up || (max_ticks != 0 && ticks() >= max_ticks); }

    // y: not a function of X only. A var not in cls with no def has the
    // function false, and is also fun_of_x
    enum class VarKind : char { unseen, fun_of_x, y };
    struct Classified {
        std::vector<VarKind> kind;
        std::vector<uint32_t> defined; // the vars of cls that already have a function
        std::vector<uint32_t> unconstrained;
    };
    static Classified classify_defined(const CoverProblem& problem, const std::vector<std::vector<CMSat::Lit>>& cls);
    static constexpr uint32_t none = std::numeric_limits<uint32_t>::max();
    // NoY::keep: per X with no Y, a clause over X that rules out its cube
    std::vector<std::vector<CMSat::Lit>> kept_cubes;

private:
    void add_vars_and_cls();
    void tie_defs();
    void add_helpers();
    void set_phases();

    bool x_cls_cex(std::vector<CMSat::lbool>& cex);
    void cex_from_x_solver(std::vector<CMSat::lbool>& cex);
    void block_no_y_cube();
    void x_solver_gets_cls();
    void refine();
    void compute_refinement(const std::vector<CMSat::lbool>& model);
    bool model_satisfies(const std::vector<CMSat::lbool>& model) const;
    ArjunNS::aig_lit y_def_cls_hold(Subst& s);
    void build_funs(Funs& funs);

    CMSat::lbool solve(MetaSolver& solver, std::vector<CMSat::Lit>* assumptions = nullptr);
    CMSat::Lit in_solvers(const CMSat::Lit l) const { return CMSat::Lit(solver_var[l.var()], l.sign()); }
    uint32_t helper_idx(const CMSat::Lit h) const { return h.var() - helper_base; }
    void new_y_var(const uint32_t v) {
        solver_var[v] = y_solver.nVars();
        y_solver.new_var();
    }
    static double frac_squared(const double num, const double of) { return num == 0 ? 0 : (num / of) * (num / of); }
    template<class F> static auto timed(double& sum, F&& fun) {
        const double start = cpuTime();
        const auto ret = fun();
        sum += cpuTime() - start;
        return ret;
    }
    void print_stats(const char* what);
    CMSat::lbool finish(const CMSat::lbool ret);

    const CoverProblem& problem;
    const ArjunNS::AIGManager& aig_mng;
    const std::vector<std::vector<CMSat::Lit>>& comp_cls;
    const Conf& cconf;
    const uint64_t max_ticks;
    bool gave_up = false;
    const uint32_t verb;
    const uint32_t num_vars;
    const bool sat_minim;
    MetaSolver x_solver, y_solver;

    // Fixed after setup.
    // The vars that already have a function. One of X only is on the x side
    // with X: x_solver picks it, tied to its function there. Any other one
    // follows the ys: `y_def_cls`, the clauses they are in, are rewritten for
    // every model. `x_side` is X, the first `num_x`, then those functions.
    std::vector<VarKind> state;
    std::vector<uint32_t> defined, unconstrained;
    std::vector<uint32_t> x_side;
    uint32_t num_x = 0;
    std::vector<char> on_x_side;

    // The solvers only get the vars they have clauses on: the x side, at
    // the same index in both, then for y_solver the rest
    std::vector<uint32_t> solver_var, y_vars;

    Subst defs_in_y, defs_in_x, defs_in_vars;
    std::vector<ArjunNS::aig_lit> aig_refs; // the encoders cache by node address
    ArjunNS::AIGToCNF<MetaSolver> enc_y, enc_x;

    uint32_t helper_base = 0;
    std::vector<Helper> helpers;
    std::vector<SplitClause> split_cls;
    std::vector<std::vector<CMSat::Lit>> y_def_cls, x_cls_solver;

    RefinementMinimizer minimizer;

    // Changed every round.
    // per refinement, for the Skolem functions: its helpers, and the model's Y
    std::vector<std::vector<CMSat::Lit>> refinements;
    std::vector<bool> ref_models;

    std::vector<CMSat::Lit> assumps, refinement;
    double budget_used = 0;
    struct Stats {
        uint64_t rounds = 0, ref_lits = 0, num_cubes = 0, cube_lits = 0, minim_removed = 0;
        double start_time = 0, setup_time = 0;
        double x_time = 0, y_time = 0, refine_time = 0, y_def_time = 0, funs_time = 0;
    } stats;
};

using Cls = std::vector<std::vector<CMSat::Lit>>;

// Clauses that share no y, directly or through a function, are covered
// apart: together they need the product of their models
struct Components {
    std::vector<Cls> comps;
    Cls x_cls; // over the x side only
    std::vector<char> on_x_side; // X, or a function of X only
};
Components split_into_components(const CoverProblem& problem, const Cls& cls);

// gone: ys whose clauses go; cubes: the clauses replacing them. Returns the clauses removed, net
int64_t rewrite_cnf_with_cubes(ArjunNS::SimplifiedCNF& cnf, const std::vector<char>& gone, Cls&& cubes);

}
