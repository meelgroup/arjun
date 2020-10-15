/******************************************
Copyright (C) 2020 Mate Soos

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
***********************************************/

#ifndef ARJUN_H__
#define ARJUN_H__

#include <cstdint>
#include <vector>
#include <utility>
#include <string>
#include <cryptominisat5/cryptominisat.h>
#include <cryptominisat5/solvertypesmini.h>

namespace ArjunNS {
    struct ArjPrivateData;
    #ifdef _WIN32
    class __declspec(dllexport) Arjun
    #else
    class Arjun
    #endif
    {
    public:
        Arjun();
        ~Arjun();
        std::string get_version_info();
        std::string get_solver_version_info();
        //void set_projection_set(const std::vector<uint32_t>& vars);
        void set_verbosity(uint32_t verb);
        void new_vars(uint32_t num);
        uint32_t nVars();
        void new_var();
        void add_xor_clause(const std::vector<uint32_t>& vars, bool rhs);
        void add_clause(const std::vector<CMSat::Lit>& lits);
        void set_seed(uint32_t seed);
        uint32_t set_starting_sampling_set(const std::vector<uint32_t>& vars);
        uint32_t start_with_clean_sampling_set();
        std::vector<uint32_t> get_indep_set();
        uint32_t get_orig_num_vars() const;

        //Get clauses
        void start_getting_small_clauses(uint32_t max_len, uint32_t max_glue, bool red = true);
        bool get_next_small_clause(std::vector<CMSat::Lit>& ret); //returns FALSE if no more
        void end_getting_small_clauses();

    private:
        ArjPrivateData* arjdata = NULL;
    };
}

#endif