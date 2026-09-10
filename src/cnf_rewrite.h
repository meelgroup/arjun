/*
 Arjun - CNF rewriting through AIG lifting

 Recovers gate definitions (AND/OR/XOR/ITE/EQUIV/irregular) syntactically
 from the clause set, lifts the recovered logic into an AIG, simplifies it
 with AIGRewriter, and writes it back with AIGToCNF. The clauses the gates
 came from are deleted. Variables that are counted over (sampling vars,
 weighted vars) are never removed; any other gate output whose every
 occurrence is inside recovered gate clauses is inlined into its consumers.

 Copyright (c) 2026, Mate Soos. MIT License.
 */

#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <cryptominisat5/solvertypesmini.h>
#include "arjun.h"
#include "config.h"

#if defined(_WIN32) || defined(__CYGWIN__)
  #define CNFRW_PUBLIC __declspec(dllexport)
#else
  #define CNFRW_PUBLIC __attribute__((visibility("default")))
#endif

namespace ArjunInt {

enum class GateType : uint8_t { AND = 0, XOR, ITE, EQUIV, IRREG, PG, NUM };
CNFRW_PUBLIC const char* gate_type_name(GateType t);
CNFRW_PUBLIC const char* fanin_bucket_name(uint32_t b);
constexpr uint32_t kFaninBuckets = 8;
CNFRW_PUBLIC uint32_t fanin_bucket(uint32_t fanin);

struct CNFRW_PUBLIC CnfRwStats {
    uint64_t cand_gates[(size_t)GateType::NUM] = {};
    uint64_t cand_inputs[(size_t)GateType::NUM] = {};
    uint64_t sel_gates[(size_t)GateType::NUM] = {};
    uint64_t sel_inputs[(size_t)GateType::NUM] = {};
    uint64_t sel_clauses[(size_t)GateType::NUM] = {};
    uint64_t fanin_hist[(size_t)GateType::NUM][kFaninBuckets] = {};
    uint64_t rej_clause_conflict = 0;
    uint64_t rej_var_defined = 0;
    uint64_t rej_cycle = 0;
    uint64_t rej_dont_elim_no_gain = 0;
    uint64_t irreg_tried = 0;
    uint64_t irreg_taut_ok = 0;
    uint64_t irreg_bf_ok = 0;
    uint64_t irreg_too_big = 0;
    uint64_t gate_outputs = 0;
    uint64_t removable_outputs = 0;
    uint64_t kept_outputs = 0;
    uint64_t kept_dont_elim = 0;
    uint64_t kept_external_use = 0;
    uint64_t leaf_vars = 0;
    uint64_t roots = 0;
    uint64_t roots_const = 0;
    uint64_t roots_leaf = 0;
    uint64_t roots_shared = 0;
    uint64_t roots_helper = 0;
    uint64_t roots_half = 0;
    uint64_t comp_accepted = 0;
    uint64_t comp_rejected = 0;
    uint64_t dead_gates = 0;
    int64_t comp_gain_cost = 0;
    uint64_t enc_aig2cnf_won = 0;
    uint64_t enc_mapper_won = 0;
    int64_t comp_rej_cost = 0;
    uint64_t max_fanin = 0;
    uint64_t aig_nodes_before = 0;
    uint64_t aig_nodes_after = 0;
    uint64_t aig_max_depth = 0;
    uint64_t cls_in = 0, lits_in = 0, vars_in = 0;
    uint64_t cls_removed = 0, lits_removed = 0;
    uint64_t cls_added = 0, lits_added = 0;
    uint64_t equiv_bins_added = 0;
    uint64_t red_cls_dropped = 0;
    uint64_t vars_removed = 0, vars_added = 0;
    uint64_t cls_out = 0, lits_out = 0, vars_out = 0;
    double t_detect = 0, t_select = 0, t_build = 0, t_rewrite = 0, t_encode = 0,
           t_assemble = 0, t_total = 0;

    void print(int verb, const std::string& prefix) const;
};

class CNFRW_PUBLIC CnfRewrite {
public:
    explicit CnfRewrite(const Config& _conf) : conf(_conf) {}
    bool run(ArjunNS::SimplifiedCNF& cnf, const std::string& tag = "");
    const CnfRwStats& get_stats() const { return stats; }

    struct Lifted {
        std::vector<ArjunNS::aig_lit> roots;
        std::vector<uint32_t> root_vars;
        std::vector<char> removable;
        std::vector<GateType> root_type;
        std::vector<uint32_t> root_gate_cls;
        std::vector<uint32_t> root_gate_lits;
        uint32_t nvars = 0;
    };
    Lifted lift_only(const ArjunNS::SimplifiedCNF& cnf);

    struct CompInfo {
        std::vector<ArjunNS::aig_lit> roots;
        std::vector<uint32_t> root_vars;
        uint32_t gates = 0;
        uint32_t removable = 0;
        uint64_t orig_lits = 0, orig_cls = 0, new_lits = 0, new_cls = 0, helpers = 0;
        bool accepted = false;
    };
    void set_collect_comp_info(bool b) { collect_comp_info = b; }
    const std::vector<CompInfo>& get_comp_info() const { return comp_info; }

private:
    struct Gate {
        GateType type = GateType::AND;
        CMSat::Lit out = CMSat::lit_Undef;
        std::vector<CMSat::Lit> ins;
        std::vector<std::vector<CMSat::Lit>> terms;
        std::vector<uint32_t> cls;
        uint32_t priority() const;
    };

    const Config& conf;
    CnfRwStats stats;
    bool collect_comp_info = false;
    std::vector<CompInfo> comp_info;

    uint32_t nvars = 0;
    std::vector<std::vector<CMSat::Lit>> cls;
    std::vector<std::vector<uint32_t>> occ;
    std::vector<uint32_t> bin_occ;
    std::unordered_map<uint64_t, uint32_t> bin_map;
    std::unordered_map<uint64_t, uint32_t> tern_map;
    std::vector<char> dont_elim;
    std::vector<char> counted;
    std::vector<char> cl_used;
    std::vector<Gate> cands;
    std::vector<int32_t> gate_of_var;
    std::vector<char> mark_buf;
    std::vector<uint32_t> pos_buf;

    void build_occ(const ArjunNS::SimplifiedCNF& cnf);
    void setup_dont_elim(const ArjunNS::SimplifiedCNF& cnf);
    void detect_and_gates();
    void detect_xor_gates();
    void detect_ite_gates();
    void detect_irreg_gates();
    void detect_pg_gates();
    int root_half_mode(uint32_t v) const;
    void select_gates();
    void break_cycles();
    bool irreg_check(uint32_t v, Gate& g);
    void verify_gates() const;
    void print_gate(const Gate& g) const;
    bool gate_eval(const Gate& g, const std::function<bool(CMSat::Lit)>& val) const;

    static uint64_t bin_key(CMSat::Lit a, CMSat::Lit b);
    static uint64_t tern_key(CMSat::Lit a, CMSat::Lit b, CMSat::Lit c);
    uint32_t find_bin(CMSat::Lit a, CMSat::Lit b) const;
    uint32_t find_tern(CMSat::Lit a, CMSat::Lit b, CMSat::Lit c) const;
    static constexpr uint32_t no_cl = std::numeric_limits<uint32_t>::max();

    ArjunNS::aig_lit gate_aig(const Gate& g, const std::vector<ArjunNS::aig_lit>& var_aig) const;
    void compute_removable(std::vector<char>& removable) const;
    void fill_root_info(Lifted& out) const;
    struct EncResult {
        std::vector<std::vector<CMSat::Lit>> cls;
        std::vector<CMSat::Lit> helper_map;
        uint32_t nv = 0, helpers = 0, n_helper = 0, n_shared = 0, n_leaf = 0, n_half = 0;
        uint64_t lits = 0;
    };
    EncResult encode_component(const std::vector<ArjunNS::aig_lit>& croots,
                               const std::vector<uint32_t>& cvars, bool use_mapper,
                               const std::vector<int>& half);
    void build_aigs(const std::vector<char>& removable, std::vector<ArjunNS::aig_lit>& var_aig,
                    std::vector<uint32_t>& root_vars, std::vector<ArjunNS::aig_lit>& roots);
    void reset();
};

}
