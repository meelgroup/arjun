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
using std::vector;
using std::setw;
using std::set;
using std::endl;
using std::cout;
using CMSat::Lit;
using std::map;

enum AIGT {t_and, t_var, t_const};
struct AIG {
    AIGT type = t_const;
    uint32_t var = std::numeric_limits<uint32_t>::max();
    bool neg = false;
    AIG* l = nullptr;
    AIG* r = nullptr;
};

struct AIGManager {
    AIGManager() {
        const_true = new AIG();
        const_true->type = t_const;
        const_true->neg = false;

        const_false = new_neg(const_false);
        aigs.push_back(const_true);
        aigs.push_back(const_false);
    }

    ~AIGManager() {
        for (auto aig : aigs) delete aig;
    }

    AIG* new_lit(Lit l) {
        return new_lit(l.var(), l.sign());
    }

    AIG* new_lit(uint32_t var, bool neg = false) {
        if (lit_to_aig.count(Lit(var, neg))) {
            return lit_to_aig.at(Lit(var, neg));
        }
        AIG* ret = new AIG();
        ret->type = t_var;
        ret->var = var;
        ret->neg = neg;
        aigs.push_back(ret);
        lit_to_aig[Lit(var, neg)] = ret;

        return ret;
    }

    AIG* new_const(bool val) {
        return val ? const_true : const_false;
    }

    AIG* new_neg(AIG* a) {
        AIG* ret = new AIG();
        ret->type = t_and;
        ret->l = a;
        ret->r = a;
        ret->neg = true;
        aigs.push_back(ret);
        return ret;
    }

    AIG* new_and(AIG* l, AIG* r) {
        AIG* ret = new AIG();
        ret->type = t_and;
        ret->l = l;
        ret->r = r;
        aigs.push_back(ret);
        return ret;
    }

    AIG* new_or(AIG* l, AIG* r) {
        AIG* ret = new AIG();
        ret->type = t_and;
        ret->neg = true;
        ret->l = new_neg(l);
        ret->r = new_neg(r);
        aigs.push_back(ret);
        return ret;
    }
    AIG* new_ite(AIG* l, AIG* r, AIG* b) {
        return new_or(new_and(b, l), new_and(new_neg(b), r));
    }

    AIG* new_ite(AIG* l, AIG* r, Lit b) {
        auto b_aig = new_lit(b.var(), b.sign());
        return new_or(new_and(b_aig, l), new_and(new_neg(b_aig), r));
    }

    vector<AIG*> aigs;
    map<Lit, AIG*> lit_to_aig;
    AIG* const_true = nullptr;
    AIG* const_false = nullptr;
};

struct FHolder {
    struct Formula {
        // TODO: we could have a flag of what has already been inserted into
        // solver_train
        std::vector<std::vector<CMSat::Lit>> clauses;
        CMSat::Lit out = CMSat::lit_Error;
        bool finished = false;
        AIG* aig = nullptr;
    };

    Formula constant_formula(bool value) {
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
        ret.aig = aig_mng.new_ite(fleft.aig, fright.aig, branch.aig);
        return ret;
    }

    Formula neg(const Formula& f) {
        Formula ret = f;
        if (solver) ret.out = ~f.out;
        ret.aig = aig_mng.new_neg(f.aig);
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
        ret.aig = aig_mng.new_or(fleft.aig, fright.aig);
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
        ret.aig = aig_mng.new_ite(fleft.aig, fright.aig, branch);
        return ret;
    }

    AIGManager aig_mng;
    CMSat::SATSolver* solver;
    Lit my_true_lit;
};

inline std::ostream& operator<<(std::ostream& os, const FHolder::Formula& f) {
    os << " ==== Formula: " << f.out << " ==== " << endl;
    for (const auto& cl : f.clauses) {
        for (const auto& l : cl) {
            os << std::setw(6) << l;
        }
        cout << " 0" << endl;
    }
    os << endl;
    os << "Output: " << f.out;
    return os;
}
