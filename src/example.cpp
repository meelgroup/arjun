#include "arjun.h"

#include <vector>
#include <iostream>
#include <limits>
#include <set>

using std::vector;
using std::cout;
using std::endl;
using std::numeric_limits;
using namespace CMSat;
using namespace ArjunNS;

int main()
{

    ArjunNS::Arjun arjun;
    arjun.new_vars(100);
    arjun.set_verbosity(0);

    vector<Lit> clause;

    //1 2 0
    clause.clear();
    clause.push_back(CMSat::Lit(0, false));
    clause.push_back(CMSat::Lit(1, false));
    arjun.add_clause(clause);

    //1 2 10 0
    clause.clear();
    clause.push_back(CMSat::Lit(0, false));
    clause.push_back(CMSat::Lit(1, false));
    clause.push_back(CMSat::Lit(9, false));
    arjun.add_clause(clause);

    //3 -4 0
    clause.clear();
    clause.push_back(CMSat::Lit(2, false));
    clause.push_back(CMSat::Lit(3, true));
    arjun.add_clause(clause);

    //3 -4  5 0
    clause.clear();
    clause.push_back(CMSat::Lit(2, false));
    clause.push_back(CMSat::Lit(3, true));
    clause.push_back(CMSat::Lit(4, true));
    arjun.add_clause(clause);

    vector<uint32_t> proj;
    for(uint32_t i = 0; i < 100; i++) proj.push_back(i);
    arjun.set_starting_sampling_set(proj);

    proj = arjun.get_indep_set();
    std::set<uint32_t> dont_elim (proj.begin(), proj.end());
    dont_elim.insert(10);
    vector<uint32_t> dont_elim_vec(dont_elim.begin(), dont_elim.end());

    arjun.get_fully_simplified_renumbered_cnf(
        dont_elim_vec,
        vector<uint32_t>(),
        100,
        false,
        false
    );

    //get cnf
    bool ret = true;
    const uint32_t orig_num_vars = arjun.get_orig_num_vars();
    arjun.start_getting_small_clauses(
        std::numeric_limits<uint32_t>::max(),
        std::numeric_limits<uint32_t>::max(),
        false);
    while (ret) {
        ret = arjun.get_next_small_clause(clause);
        if (!ret) {
            break;
        }

        bool ok = true;
        for(auto l: clause) {
            if (l.var() >= orig_num_vars) {
                ok = false;
                break;
            }
        }

        if (ok) {
            cout << "clause: ";
            for(const auto& l: clause) {
                int lit = l.var()+1;
                if (l.sign()) lit *= -1;
                cout << lit << " ";
            }
            cout << "0" << endl;
        }
    }
    arjun.end_getting_small_clauses();

    return 0;
}
