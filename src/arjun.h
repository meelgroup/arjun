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

#pragma once

#include <cstdint>
#include <vector>
#include <string>
#include <mpfr.h>
#include <set>
#include <fstream>
#include <gmpxx.h>
#ifdef CMS_LOCAL_BUILD
#include "cryptominisat.h"
#else
#include <cryptominisat5/cryptominisat.h>
#endif

namespace ArjunNS {
    struct SimpConf {
        bool oracle_vivify = true;
        bool oracle_vivify_get_learnts = true;
        bool oracle_sparsify = true;
        int iter1 = 2;
        int iter2 = 2;
        int bve_grow_iter1 = 0;
        int bve_grow_iter2 = 6;
        bool appmc = false;
        int bve_too_large_resolvent = -1;
    };

    struct SimplifiedCNF {
        std::vector<std::vector<CMSat::Lit>> clauses;
        std::vector<std::vector<CMSat::Lit>> red_clauses;
        std::vector<uint32_t> sampl_vars;
        // for minimize this is set to orig sampling set,
        // for extend, this is extended, and the weights of the extend are set to 0.5/0.5
        std::vector<uint32_t> opt_sampl_vars;
        uint32_t nvars = 0;
        mpq_class multiplier_weight = 1;
        bool weighted = false;
        bool backbone_done = false;
        struct Weight {mpq_class pos = 1; mpq_class neg = 1;};
        std::map<uint32_t, Weight> weights;

        uint32_t nVars() const { return nvars; }
        uint32_t new_vars(uint32_t vars) { nvars+=vars; return nvars; }
        uint32_t new_var() { nvars++; return nvars; }

        void start_with_clean_sampl_vars() {
            assert(sampl_vars.empty());
            assert(opt_sampl_vars.empty());
            for(uint32_t i = 0; i < nvars; i++) sampl_vars.push_back(i);
            for(uint32_t i = 0; i < nvars; i++) opt_sampl_vars.push_back(i);
        }
        void add_xor_clause(std::vector<uint32_t>&, bool) { exit(-1); }
        void add_xor_clause(std::vector<CMSat::Lit>&, bool) { exit(-1); }
        void add_clause(std::vector<CMSat::Lit>& cl) { clauses.push_back(cl); }
        void add_red_clause(std::vector<CMSat::Lit>& cl) { red_clauses.push_back(cl); }
        bool get_sampl_vars_set() const { return sampl_vars_set; }
        bool sampl_vars_set = false;
        bool opt_sampl_vars_given = false;
        template<class T>
        void set_sampl_vars(const T& vars, bool ignore = false) {
            if (!ignore) {
                assert(sampl_vars.empty());
                assert(sampl_vars_set == false);
            }
            sampl_vars.clear();
            sampl_vars_set = true;
            sampl_vars.insert(sampl_vars.begin(), vars.begin(), vars.end());
        }
        const auto& get_sampl_vars() const { return sampl_vars; }
        template<class T>
        void set_opt_sampl_vars(const T& vars) {
            assert(opt_sampl_vars.empty());
            assert(opt_sampl_vars_given == false);
            opt_sampl_vars_given = true;
            opt_sampl_vars.insert(opt_sampl_vars.begin(), vars.begin(), vars.end());
        }

        void set_multiplier_weight(const mpq_class& m) { multiplier_weight = m; }
        auto get_multiplier_weight() const { return multiplier_weight; }
        mpq_class get_lit_weight(CMSat::Lit lit) const {
            assert(weighted);
            auto it = weights.find(lit.var());
            if (it == weights.end()) return 1;
            else {
                if (!lit.sign()) return it->second.pos;
                else return it->second.neg;
            }
        }
        void unset_var_weight(uint32_t v) {
            auto it = weights.find(v);
            if (it != weights.end()) weights.erase(it);
        }
        void set_lit_weight(CMSat::Lit lit, const mpq_class& w) {
            assert(weighted);
            auto it = weights.find(lit.var());
            if (it == weights.end()) {
                Weight weight;
                if (lit.sign()) {weight.neg = w;weight.pos = 1.0-w;}
                else {weight.pos = w;weight.neg = 1.0-w;}
                weights[lit.var()] = weight;
                return;
            } else {
                if (!lit.sign()) it->second.pos = w;
                else it->second.neg = w;
            }
        }
        void set_weighted(bool _weighted) { weighted = _weighted; }
        bool get_weighted() const { return weighted; }

        std::vector<CMSat::Lit>& map_cl(std::vector<CMSat::Lit>& cl, std::vector<uint32_t> v_map) {
                for(auto& l: cl) l = CMSat::Lit(v_map[l.var()], l.sign());
                return cl;
        }
        std::vector<uint32_t>& map_var(std::vector<uint32_t>& cl, std::vector<uint32_t> v_map) {
            for(auto& l: cl) l = v_map[l];
            return cl;
        }
        std::set<uint32_t> map_var(const std::set<uint32_t>& cl, std::vector<uint32_t> v_map) {
            std::set<uint32_t> new_set;
            for(auto& l: cl) new_set.insert(v_map[l]);
            return new_set;
        }

        // renumber variables such that sampling set start from 0...N
        void renumber_sampling_vars_for_ganak() {
            assert(sampl_vars.size() <= opt_sampl_vars.size());
            constexpr uint32_t m = std::numeric_limits<uint32_t>::max();
            std::vector<uint32_t> map_here_to_there(nvars, m);
            uint32_t i = 0;
            for(const auto& v: sampl_vars) {
                assert(v < nvars);
                map_here_to_there[v] = i;
                i++;
            }

            for(const auto& v: opt_sampl_vars) {
                assert(v < nvars);
                if (map_here_to_there[v] == m) {
                    map_here_to_there[v] = i;
                    i++;
                }
            }

            // Go through the rest of the variables not in sampling set.
            for(uint32_t x = 0; x < nvars; x++) {
                if (map_here_to_there[x] == m) {
                    map_here_to_there[x] = i;
                    i++;
                }
            }
            assert(i == nvars);

            // Now we renumber
            sampl_vars = map_var(sampl_vars, map_here_to_there);
            opt_sampl_vars = map_var(opt_sampl_vars, map_here_to_there);
            for(auto& cl: clauses) map_cl(cl, map_here_to_there);
            for(auto& cl: red_clauses) map_cl(cl, map_here_to_there);
            if (weighted) {
                std::map<uint32_t, Weight> new_weights;
                for(auto& w: weights)
                    new_weights[map_here_to_there[w.first]] = w.second;
            }
        }


        void write_simpcnf(const std::string& fname,
                    bool red = true) const
        {
            uint32_t num_cls = clauses.size();
            std::ofstream outf;
            outf.open(fname.c_str(), std::ios::out);
            outf << "p cnf " << nvars << " " << num_cls << std::endl;
            if (weighted) outf << "c t wmc" << std::endl;

            //Add projection
            outf << "c p show ";
            auto sampl = sampl_vars;
            std::sort(sampl.begin(), sampl.end());
            for(const auto& v: sampl) {
                assert(v < nvars);
                outf << v+1  << " ";
            }
            outf << "0\n";
            outf << "c p optshow ";
            sampl = opt_sampl_vars;
            std::sort(sampl.begin(), sampl.end());
            for(const auto& v: sampl) {
                assert(v < nvars);
                outf << v+1  << " ";
            }
            outf << "0\n";

            for(const auto& cl: clauses) outf << cl << " 0\n";
            if (red) for(const auto& cl: red_clauses)
                outf << "c red " << cl << " 0\n";

            if (weighted) {
                for(const auto& it: weights) {
                    outf << "c p weight " << CMSat::Lit(it.first,false) << " "
                        << it.second.pos << " 0" << std::endl;
                    outf << "c p weight " << CMSat::Lit(it.first,true) << " "
                        << it.second.neg << " 0" << std::endl;
                }
            }
            outf << "c MUST MULTIPLY BY " << multiplier_weight << std::endl;
        }
    };

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
        static std::string get_version_info();
        static std::string get_sbva_version_info();
        static std::string get_compilation_env();
        static std::string get_solver_version_info();

        // Perform indep set calculation
        void only_run_minimize_indep(SimplifiedCNF& cnf);
        void only_run_minimize_indep_synth(SimplifiedCNF& cnf);
        void only_extend_sampl_vars(SimplifiedCNF& cnf);
        void only_unsat_define(SimplifiedCNF& cnf);
        void only_unate(SimplifiedCNF& cnf);

        void elim_to_file(SimplifiedCNF& cnf, bool all_indep,
            bool do_extend_indep, bool do_bce,
            bool do_unate, const SimpConf& simp_conf,
            int64_t sbva_steps, uint32_t sbva_cls_cutoff, uint32_t sbva_lits_cutoff, int sbva_tiebreak);
        SimplifiedCNF only_get_simplified_cnf(const SimplifiedCNF& cnf, const SimpConf& simp_conf);
        void only_bce(SimplifiedCNF& cnf);
        void only_reverse_bce(SimplifiedCNF& cnf);
        void only_backbone(SimplifiedCNF& cnf);
        const SimplifiedCNF& get_orig_cnf() const;
        void only_run_sbva(SimplifiedCNF& orig,
            int64_t sbva_steps = 200, uint32_t sbva_cls_cutoff = 2,
            uint32_t sbva_lits_cutoff = 2, int sbva_tiebreak = 1);

        //Set config
        void set_verb(uint32_t verb);
        void set_distill(bool distill);
        void set_intree(bool intree);
        void set_simp(bool simp);
        void set_bve_pre_simplify(bool bve_pre_simp);
        void set_unknown_sort(uint32_t unknown_sort);
        void set_incidence_count(uint32_t incidence_count);
        void set_or_gate_based(bool or_gate_based);
        void set_xor_gates_based(bool xor_gates_based);
        void set_probe_based(bool probe_based);
        void set_backward(bool backward);
        void set_backw_max_confl(uint32_t backw_max_confl);
        void set_gauss_jordan(bool gauss_jordan);
        void set_find_xors(bool find_xors);
        void set_ite_gate_based(bool ite_gate_based);
        void set_do_unate(bool do_unate);
        void set_irreg_gate_based(const bool irreg_gate_based);
        void set_gate_sort_special(bool gate_sort_special);
        //void set_polar_mode(CMSat::PolarityMode mode);
        void set_no_gates_below(double no_gates_below);
        void set_specified_order_fname(std::string specified_order_fname);
        void set_bce(const bool bce);
        void set_weighted(const bool);
        void set_extend_max_confl(uint32_t extend_max_confl);

        //Get config
        uint32_t get_verb() const;
        bool get_do_unate() const;
        std::string get_specified_order_fname() const;
        double get_no_gates_below() const;
        bool get_simp() const;
        bool get_distill() const;
        bool get_intree() const;
        bool get_bve_pre_simplify() const;
        uint32_t get_incidence_count() const;
        uint32_t get_unknown_sort() const;
        bool get_or_gate_based() const;
        bool get_xor_gates_based() const;
        bool get_probe_based() const;
        bool get_backward() const;
        uint32_t get_backw_max_confl() const;
        bool get_gauss_jordan() const;
        bool get_find_xors() const;
        bool get_ite_gate_based() const;
        bool get_irreg_gate_based() const;
        bool get_gate_sort_special() const;
        bool get_bce() const;
        uint32_t get_extend_max_confl() const;

    private:
        ArjPrivateData* arjdata = nullptr;
    };
}
