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

#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

#include <vector>
#include <set>
#include <iostream>
#include <iomanip>
#include "arjun.h"
using std::vector;
using std::setw;
using std::set;
using std::endl;
using std::cout;
using CMSat::Lit;
using CMSat::lit_Error;
using CMSat::SATSolver;
using std::map;

namespace ArjunNS {

class FHolder {
public:
    FHolder() = delete;
    FHolder(SATSolver* _solver) : solver(_solver) {
        solver->new_var();
        my_true_lit = Lit(solver->nVars()-1, false);
        solver->add_clause({my_true_lit});
    }
    struct Formula {
        // TODO: we could have a flag of what has already been inserted into
        // solver_train
        vector<std::vector<Lit>> clauses;
        bool already_added_to_manthans_solver = false;
        Lit out = lit_Error;
        bool finished = false;
        aig_ptr aig = nullptr;
    };

    Formula constant_formula(const bool value) {
        Formula ret;
        if (solver) ret.out = value ? my_true_lit : ~my_true_lit;
        ret.aig = aig_mng.new_const(value);
        return ret;
    }

    Formula compose_ite(const Formula& fleft, const Formula& fright, const Formula& branch) {
        Formula ret;
        if (solver) {
            ret = compose_ite(fleft, fright, branch.out);
            ret.clauses.insert(ret.clauses.end(), branch.clauses.begin(), branch.clauses.end());
        }
        ret.aig = AIG::new_ite(fleft.aig, fright.aig, branch.aig);
        return ret;
    }

    Formula neg(const Formula& f) {
        Formula ret = f;
        if (solver) ret.out = ~f.out;
        ret.aig = AIG::new_not(f.aig);
        return ret;
    }

    Formula compose_and(const Formula& fleft, const Formula& fright) {
        return neg(compose_or(neg(fleft), neg(fright)));
    }

    Formula compose_or(const Formula& fleft, const Formula& fright) {
        Formula ret;
        if (solver) {
            ret.clauses = fleft.clauses;
            for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);

            solver->new_var();
            uint32_t fresh_v = solver->nVars()-1;
            Lit l = Lit(fresh_v, false);

            ret.clauses.push_back({~l, fleft.out, fright.out});
            ret.clauses.push_back({l, ~fleft.out});
            ret.clauses.push_back({l, ~fright.out});
            ret.out = l;
        }
        ret.aig = AIG::new_or(fleft.aig, fright.aig);
        return ret;
    }

    Formula compose_ite(const Formula& fleft, const Formula& fright, Lit branch) {
        Formula ret;
        if (solver) {
            ret.clauses = fleft.clauses;
            for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);
            solver->new_var();
            uint32_t fresh_v = solver->nVars()-1;
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
            Lit b = branch;
            Lit l = fleft.out;
            Lit r = fright.out;
            Lit fresh = Lit(fresh_v, false);
            ret.clauses.push_back({~b, fresh, ~l});
            ret.clauses.push_back({~b, ~fresh, l});
            ret.clauses.push_back({b, fresh, ~r});
            ret.clauses.push_back({b, ~fresh, r});
            ret.out = Lit(fresh_v, false);
        }
        ret.aig = AIG::new_ite(fleft.aig, fright.aig, branch);
        return ret;
    }

    Lit get_true_lit() const {
        assert(my_true_lit != lit_Error);
        return my_true_lit;
    }

private:
    AIGManager aig_mng;
    SATSolver* solver = nullptr;
    Lit my_true_lit = lit_Error;
};

}

inline std::ostream& operator<<(std::ostream& os, const ArjunNS::FHolder::Formula& f) {
    os << " === Formula out: " << f.out << " === " << endl;
    for (const auto& cl : f.clauses) {
        for (const auto& l : cl) {
            os << std::setw(6) << l;
        }
        cout << " 0" << endl;
    }
    os << " === End Formula === ";
    return os;
}
