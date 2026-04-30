/*
 Arjun

 Copyright (c) 2019, Mate Soos and Kuldeep S. Meel. All rights reserved.

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

#include <cryptominisat5/cryptominisat.h>
#include <vector>
#include <set>
#include <iostream>
#include <iomanip>
#include "arjun.h"
#include "metasolver2.h"
namespace ArjunInt {

struct CL {
    constexpr CL(const std::vector<CMSat::Lit>& _lits) : lits(_lits) {}
    std::vector<CMSat::Lit> lits;
    bool inserted = false;
};

template<typename T>
class FHolder {
public:
    FHolder() = delete;
    FHolder(T* _solver) : solver(_solver) {
        solver->new_var();
        my_true_lit = CMSat::Lit(solver->nVars()-1, false);
        solver->add_clause({my_true_lit});
    }
    struct Formula {
        // TODO: we could have a flag of what has already been inserted into
        // solver_train
        std::vector<CL> clauses;
        // Index hint: clauses[0..uninserted_start) are guaranteed to have
        // already been pushed to the cex_solver. inject_formulas walks from
        // this index forward and sets it to clauses.size() at the end,
        // turning the per-iteration "skip already-inserted" linear scan
        // into a tight tail-iteration. Clauses are only ever appended (in
        // perform_repair / compose_or-move), so the prefix invariant
        // holds automatically.
        uint32_t uninserted_start = 0;
        CMSat::Lit out = CMSat::lit_Error;
        ArjunNS::aig_ptr aig = nullptr;
    };

    std::set<uint32_t> get_dependent_vars(const Formula& f, uint32_t v) const {
        std::set<uint32_t> ret;
        ArjunNS::AIG::get_dependent_vars(f.aig, ret, v);
        return ret;
    }

    Formula constant_formula(const bool value) {
        Formula ret;
        ret.out = value ? my_true_lit : ~my_true_lit;
        ret.aig = aig_mng.new_const(value);
        return ret;
    }

    Formula compose_ite(const Formula& fleft, const Formula& fright, const Formula& branch, std::set<uint32_t>& helpers) {
        // ITE(branch, TRUE, x) = OR(branch, x)
        if (fleft.out == my_true_lit && fleft.clauses.empty()) {
            return compose_or(branch, fright, helpers);
        }
        // ITE(branch, FALSE, x) = AND(NOT(branch), x)
        if (fleft.out == ~my_true_lit && fleft.clauses.empty()) {
            return compose_and(neg(branch), fright, helpers);
        }
        // ITE(branch, x, TRUE) = OR(NOT(branch), x)
        if (fright.out == my_true_lit && fright.clauses.empty()) {
            return compose_or(neg(branch), fleft, helpers);
        }
        // ITE(branch, x, FALSE) = AND(branch, x)
        if (fright.out == ~my_true_lit && fright.clauses.empty()) {
            return compose_and(branch, fleft, helpers);
        }
        Formula ret;
        ret = compose_ite(fleft, fright, branch.out, helpers);
        ret.clauses.insert(ret.clauses.end(), branch.clauses.begin(), branch.clauses.end());
        ret.aig = ArjunNS::AIG::new_ite(fleft.aig, fright.aig, branch.aig);
        return ret;
    }

    Formula neg(const Formula& f) {
        Formula ret = f;
        ret.out = ~f.out;
        ret.aig = ArjunNS::AIG::new_not(f.aig);
        return ret;
    }

    // Direct AND encoding: out ↔ (left AND right).
    // Caller passes a `helpers` set so the fresh Tseitin var gets tracked;
    // Manthan::check_functions_for_y_vars otherwise asserts on the
    // unregistered literal appearing in a formula clause.
    Formula compose_and(const Formula& fleft, const Formula& fright, std::set<uint32_t>& helpers) {
        // AND(FALSE, x) = FALSE, AND(x, FALSE) = FALSE
        if (fleft.out == ~my_true_lit && fleft.clauses.empty()) return fleft;
        if (fright.out == ~my_true_lit && fright.clauses.empty()) return fright;
        // AND(TRUE, x) = x, AND(x, TRUE) = x
        if (fleft.out == my_true_lit && fleft.clauses.empty()) return fright;
        if (fright.out == my_true_lit && fright.clauses.empty()) return fleft;
        Formula ret;
        ret.clauses = fleft.clauses;
        for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);

        solver->new_var();
        uint32_t fresh_v = solver->nVars()-1;
        helpers.insert(fresh_v);
        CMSat::Lit l = CMSat::Lit(fresh_v, false);

        // l ↔ (fleft.out AND fright.out)
        ret.clauses.push_back(CL({~l, fleft.out}));
        ret.clauses.push_back(CL({~l, fright.out}));
        ret.clauses.push_back(CL({l, ~fleft.out, ~fright.out}));
        ret.out = l;

        assert(fleft.aig != nullptr);
        assert(fright.aig != nullptr);
        ret.aig = ArjunNS::AIG::new_and(fleft.aig, fright.aig);
        return ret;
    }

    // Move-aware overload: takes ownership of fright (typically the
    // accumulated big formula in perform_repair). Avoids copying
    // |fright.clauses| every iteration — over a long repair sequence the
    // const-ref version was O(N²) in clauses copied (each repair copies
    // every previously-accumulated clause).
    Formula compose_and(const Formula& fleft, Formula&& fright, std::set<uint32_t>& helpers) {
        // Constant-fold cases: defer to copy-overload to avoid surprising
        // moved-from semantics on degenerate inputs.
        if (fleft.out == ~my_true_lit && fleft.clauses.empty()) return fleft;
        if (fright.out == ~my_true_lit && fright.clauses.empty()) return Formula(std::move(fright));
        if (fleft.out == my_true_lit && fleft.clauses.empty()) return Formula(std::move(fright));
        if (fright.out == my_true_lit && fright.clauses.empty()) return fleft;

        Formula ret;
        // Move fright's clauses, append fleft's. The OR/AND helper clauses
        // get appended at the end. This makes the per-call cost O(|fleft|)
        // instead of O(|fleft| + |fright|).
        const uint32_t fright_uninserted = fright.uninserted_start;
        ret.clauses = std::move(fright.clauses);
        ret.clauses.reserve(ret.clauses.size() + fleft.clauses.size() + 3);
        for(const auto& cl: fleft.clauses) ret.clauses.push_back(cl);

        solver->new_var();
        uint32_t fresh_v = solver->nVars()-1;
        helpers.insert(fresh_v);
        CMSat::Lit l = CMSat::Lit(fresh_v, false);

        ret.clauses.push_back(CL({~l, fleft.out}));
        ret.clauses.push_back(CL({~l, fright.out}));
        ret.clauses.push_back(CL({l, ~fleft.out, ~fright.out}));
        ret.out = l;
        // Carry over the prefix-inserted invariant from fright. Anything we
        // appended (fleft's copy + 3 helpers) is freshly emitted and not yet
        // pushed to cex_solver.
        ret.uninserted_start = fright_uninserted;

        assert(fleft.aig != nullptr);
        assert(fright.aig != nullptr);
        ret.aig = ArjunNS::AIG::new_and(fleft.aig, fright.aig);
        return ret;
    }

    // See compose_and for the `helpers` rationale.
    Formula compose_or(const Formula& fleft, const Formula& fright, std::set<uint32_t>& helpers) {
        // OR(TRUE, x) = TRUE
        if (fleft.out == my_true_lit && fleft.clauses.empty()) return fleft;
        if (fright.out == my_true_lit && fright.clauses.empty()) return fright;
        // OR(FALSE, x) = x, OR(x, FALSE) = x
        if (fleft.out == ~my_true_lit && fleft.clauses.empty()) return fright;
        if (fright.out == ~my_true_lit && fright.clauses.empty()) return fleft;

        Formula ret;
        ret.clauses = fleft.clauses;
        for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);

        solver->new_var();
        uint32_t fresh_v = solver->nVars()-1;
        helpers.insert(fresh_v);
        CMSat::Lit l = CMSat::Lit(fresh_v, false);

        ret.clauses.push_back(CL({~l, fleft.out, fright.out}));
        ret.clauses.push_back(CL({l, ~fleft.out}));
        ret.clauses.push_back(CL({l, ~fright.out}));
        ret.out = l;

        assert(fleft.aig != nullptr);
        assert(fright.aig != nullptr);
        ret.aig = ArjunNS::AIG::new_or(fleft.aig, fright.aig);
        return ret;
    }

    // Move-aware overload — see compose_and(fleft, Formula&&, ...).
    Formula compose_or(const Formula& fleft, Formula&& fright, std::set<uint32_t>& helpers) {
        if (fleft.out == my_true_lit && fleft.clauses.empty()) return fleft;
        if (fright.out == my_true_lit && fright.clauses.empty()) return Formula(std::move(fright));
        if (fleft.out == ~my_true_lit && fleft.clauses.empty()) return Formula(std::move(fright));
        if (fright.out == ~my_true_lit && fright.clauses.empty()) return fleft;

        Formula ret;
        const uint32_t fright_uninserted = fright.uninserted_start;
        ret.clauses = std::move(fright.clauses);
        ret.clauses.reserve(ret.clauses.size() + fleft.clauses.size() + 3);
        for(const auto& cl: fleft.clauses) ret.clauses.push_back(cl);

        solver->new_var();
        uint32_t fresh_v = solver->nVars()-1;
        helpers.insert(fresh_v);
        CMSat::Lit l = CMSat::Lit(fresh_v, false);

        ret.clauses.push_back(CL({~l, fleft.out, fright.out}));
        ret.clauses.push_back(CL({l, ~fleft.out}));
        ret.clauses.push_back(CL({l, ~fright.out}));
        ret.out = l;
        ret.uninserted_start = fright_uninserted;

        assert(fleft.aig != nullptr);
        assert(fright.aig != nullptr);
        ret.aig = ArjunNS::AIG::new_or(fleft.aig, fright.aig);
        return ret;
    }

    Formula compose_ite(const Formula& fleft, const Formula& fright, const CMSat::Lit branch, std::set<uint32_t>& helpers) {
        Formula ret;
        ret.clauses = fleft.clauses;
        for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);
        solver->new_var();
        const uint32_t fresh_v = solver->nVars()-1;
        helpers.insert(fresh_v);
        //  branch -> return left
        // !branch -> return right
        //
        //  b -> fresh = left
        // !b -> fresh = right
        //
        // !b V    f V -left
        // -b V   -f V  left
        //  b V    f V -right
        //  b V   -f V  right
        //
        CMSat::Lit b = branch;
        CMSat::Lit l = fleft.out;
        CMSat::Lit r = fright.out;
        CMSat::Lit fresh = CMSat::Lit(fresh_v, false);
        ret.clauses.push_back(CL({~b, fresh, ~l}));
        ret.clauses.push_back(CL({~b, ~fresh, l}));
        ret.clauses.push_back(CL({b, fresh, ~r}));
        ret.clauses.push_back(CL({b, ~fresh, r}));
        ret.out = CMSat::Lit(fresh_v, false);
        ret.aig = ArjunNS::AIG::new_ite(fleft.aig, fright.aig, branch);
        return ret;
    }

    CMSat::Lit get_true_lit() const {
        assert(my_true_lit != CMSat::lit_Error);
        return my_true_lit;
    }

private:
    ArjunNS::AIGManager aig_mng;
    T* solver = nullptr;
    CMSat::Lit my_true_lit = CMSat::lit_Error;
};

inline std::ostream& operator<<(std::ostream& os, const FHolder<ArjunInt::MetaSolver2>::Formula& f) {
    os << " === Formula out: " << f.out << " === " << std::endl;
    for (const auto& cl : f.clauses) {
        for (const auto& l : cl.lits) os << std::setw(6) << l;
        std::cout << " 0" << std::endl;
    }
    os << "AIG: " << f.aig << std::endl;
    os << " === End Formula === ";
    return os;
}

}
