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


struct FormulaHolder {
    struct Formula {
        // TODO: we could have a flag of what has already been inserted into
        // solver_train
        std::vector<std::vector<CMSat::Lit>> clauses;
        CMSat::Lit out = CMSat::lit_Error; // member of inter_vs
    };


    Formula constant_formula(int value) {
        Formula ret;
        ret.out = value ? my_true_lit : ~my_true_lit;
        return ret;
    }


    Formula compose_ite(const Formula& fleft, const Formula& fright, const Formula& branch) {
        Formula ret = compose_ite(fleft, fright, branch.out);
        ret.clauses.insert(ret.clauses.end(), branch.clauses.begin(), branch.clauses.end());
        return ret;
    }

    Formula neg(const Formula& f) {
        Formula ret = f;
        ret.out = ~f.out;
        return ret;
    }

    Formula compose_and(const Formula& fleft, const Formula& fright) {
        return neg(compose_or(neg(fleft), neg(fright)));
    }

    Formula compose_or(const Formula& fleft, const Formula& fright) {
        Formula ret;
        ret.clauses = fleft.clauses;
        for(const auto& cl: fright.clauses) ret.clauses.push_back(cl);

        solver->new_var();
        uint32_t fresh_v = solver->nVars()-1;
        Lit fl = Lit(fresh_v, false);

        ret.clauses.push_back({~fl, fleft.out, fright.out});
        ret.clauses.push_back({fl, ~fleft.out});
        ret.clauses.push_back({fl, ~fright.out});

        ret.out = fl;

        return ret;
    }

    Formula compose_ite(const Formula& fleft, const Formula& fright, Lit branch) {
        Formula ret;
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

        return ret;
    }

    CMSat::SATSolver* solver;
    Lit my_true_lit;
};


inline std::ostream& operator<<(std::ostream& os, const FormulaHolder::Formula& f) {
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

