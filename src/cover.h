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
#include <optional>
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

// Flips a y that no clause needs, at this X, if the other value satisfies the
// y part of more clauses with an x side. No SAT call
class Flipper {
public:
    Flipper() = default;
    // cls in y_solver's numbering, its x side the vars below num_x_side
    Flipper(const std::vector<std::vector<CMSat::Lit>>& cls, const std::vector<char>& can_flip, uint32_t num_x_side);
    // true if it flipped something
    bool flip(std::vector<CMSat::lbool>& model);
    uint64_t flips = 0;

private:
    uint32_t num_x_side = 0;
    std::vector<std::vector<CMSat::Lit>> cls; // the ones with a var to flip
    std::vector<char> has_x;
    std::vector<std::vector<uint32_t>> occ; // per literal, its clauses
    std::vector<uint32_t> flip_vars, num_true, num_y_true;
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

// subsumed_by[b]: the helpers whose x part is a subset of b's. With one of
// them in a refinement, b says nothing more
class HelperSubsumption {
public:
    HelperSubsumption() = default;
    HelperSubsumption(const std::vector<Helper>& helpers, int64_t work);
    void drop(std::vector<CMSat::Lit>& refinement, uint32_t helper_base);
    uint64_t subsumed = 0;

private:
    std::vector<std::vector<uint32_t>> subsumed_by;
    std::vector<char> in_refinement;
    std::vector<CMSat::Lit> kept;
};

// The covering of clauses that share ys. x_solver picks an X no model
// settles yet, y_solver gives a model of the clauses for it
class CoverComponent {
public:
    CoverComponent(const CoverProblem& _problem, const ArjunNS::AIGManager& _aig_mng, const std::vector<std::vector<CMSat::Lit>>& _comp_cls,
            const ArjunNS::Arjun::CoverConf& _cconf, const uint64_t _max_ticks, const uint32_t _verb) :
        problem(_problem), aig_mng(_aig_mng), comp_cls(_comp_cls), cconf(_cconf), max_ticks(_max_ticks), verb(_verb),
        num_vars(_problem.size()), sat_minim(_cconf.minim & 1), flip_minim(_cconf.minim & 2), subs_minim(_cconf.minim & 4),
        defs_in_y(_problem), defs_in_x(_problem), defs_in_vars(_problem), enc_y(y_solver), enc_x(x_solver) {}

    using Funs = std::vector<std::pair<uint32_t, ArjunNS::aig_lit>>;
    // All of it in the numbering of `problem`
    struct Result {
        CMSat::lbool ret = CMSat::l_Undef;
        std::vector<CMSat::lbool> cex; // l_False: an X with no Y
        Funs funs; // l_True and need_funs: the functions found, for the caller to set
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
    // keep_cubes: per X with no Y, a clause over X that rules out its cube
    std::vector<std::vector<CMSat::Lit>> kept_cubes;

private:
    void add_vars_and_cls();
    void tie_defs();
    void add_helpers();
    void set_phases();
    void init_flip();

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
    const ArjunNS::Arjun::CoverConf& cconf;
    const uint64_t max_ticks;
    bool gave_up = false;
    const uint32_t verb;
    const uint32_t num_vars;
    const bool sat_minim, flip_minim, subs_minim;
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

    Flipper flipper;
    RefinementMinimizer minimizer;
    HelperSubsumption subsumption;

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

// Covers the X space with models of cnf's clauses: a model settles
// every X that satisfies the universal parts of the clauses its Y leaves
// unsatisfied. This is the CEGAR of the 2QBF literature. l_True: the
// vars with no def yet got their Skolem functions, l_Undef: gave up. An X
// with no Y is returned in `cex` with l_False if stop_at_cex, else its
// cube is skipped, and x_solver gets the clauses so that no more come up.
// The limits and the ways a refinement is shortened: see Arjun::CoverConf.
//
// The defs that cnf already has are kept, and used: a model is then the
// values of the vars with no def, and it settles the X for which the
// clauses hold with the defined vars following their defs.
class Cover {
public:
    Cover(const Config& _conf, const ArjunNS::Arjun::CoverConf& _cconf, ArjunNS::SimplifiedCNF& _cnf) :
        conf(_conf), cconf(_cconf), cnf(_cnf), trans(std::in_place, _cnf), problem(trans->problem(_cnf)) {}
    // For counting: no defs, the CNF's own numbering, xs are X
    Cover(const Config& _conf, const ArjunNS::Arjun::CoverConf& _cconf, ArjunNS::SimplifiedCNF& _cnf,
            const std::vector<uint32_t>& xs) :
        conf(_conf), cconf(_cconf), cnf(_cnf), problem(_cnf.nVars(), xs) {}
    CMSat::lbool run(std::vector<CMSat::lbool>& cex);

    // A component C whose existentials Y_C occur nowhere else, with every X
    // of the clauses of X only, psi, having a Y_C, is removed: ∃Y psi ∧ C ∧
    // rest = psi ∧ ∃Y rest. With keep_cubes, C is replaced by the clauses
    // that rule out the cubes of X with no Y_C, if they are few. Each one is
    // checked against psi only, never against the others, which may go too.
    // A component with a weighted existential stays: its weights would go.
    // Returns the clauses removed, net
    int64_t drop_covered();

private:
    using Cls = std::vector<std::vector<CMSat::Lit>>;
    void split_into_components();
    CMSat::lbool cover_components(std::vector<CMSat::lbool>& cex);
    CMSat::lbool cover_one(const Cls& comp_cls, const uint32_t verb,
            std::vector<CMSat::lbool>& cex);
    void set_funs();

    // drop_covered()
    struct DropStats {
        uint32_t tried = 0, dropped = 0, replaced = 0, no_y = 0, gave_up = 0, weighted = 0, kept_def = 0;
        uint64_t cube_cls = 0, cube_lits = 0;
        uint32_t up_ticks = 0, up_cubes = 0, out_of_budget = 0;
        uint64_t done_ticks = 0, max_done_ticks = 0, up_ticks_used = 0, confl = 0;
        double max_comp_t = 0;
        void print(size_t num_comps, int64_t removed, size_t vars_gone, uint64_t used_ticks, double start) const;
    };
    // A component only needs the part of psi that its X reach, through the X
    // psi's clauses share: the rest is satisfiable apart from it, or nothing
    // is counted anyway
    class PsiReach {
    public:
        PsiReach(const Cls& psi, uint32_t num_vars);
        // appends to comp_cls the clauses of psi its X reach
        void add_reached(const std::vector<char>& is_x, Cls& comp_cls);
    private:
        const Cls& psi;
        UnionFind uf;
        std::vector<std::vector<uint32_t>> psi_of; // per root, its clauses
        std::vector<char> root_seen;
        std::vector<uint32_t> roots;
    };
    struct Covered {
        CMSat::lbool ret = CMSat::l_Undef;
        Cls cubes; // keep_cubes: per X-cube with no Y, a clause that rules it out
    };
    // what becomes of a component. keep_def: kept as its defined var beats the cubes
    enum class Action { keep, keep_def, drop, replace };
    Covered cover_for_drop(Cls& comp_cls, bool has_def, PsiReach& psi, DropStats& drop_stats);
    Action choose_action(const Covered& covered, bool has_def, size_t num_cls) const;
    // gone: the ys of the components that went; cubes: the clauses replacing them
    int64_t rewrite_cnf_with_cubes(const std::vector<char>& gone, Cls&& cubes);

    const Config& conf;
    const ArjunNS::Arjun::CoverConf& cconf;
    ArjunNS::SimplifiedCNF& cnf;
    const std::optional<OrigTranslation> trans; // none for counting
    const CoverProblem problem;

    std::vector<Cls> components;
    Cls x_cls;
    CoverComponent::Funs found_funs;
    uint64_t used_ticks = 0;
};

}
