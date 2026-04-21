/*
 Arjun - Shared random AIG generators for fuzz drivers.

 Header-only so the individual fuzz executables pull just what they need
 without adding a new library. Each generator takes an AIGManager by
 reference (for constants), a PRNG, and shape parameters. They return a
 freshly constructed AIG; caller is responsible for further use.

 Callers also get a one-stop `gen_random_shape` that picks a shape with a
 weighted distribution matching what the aig_to_cnf fuzzer has historically
 used — so the rewrite fuzzer, the aig-to-cnf fuzzer, and any future driver
 see the same corpus and the same shape biases.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#pragma once

#include "arjun.h"
#include <algorithm>
#include <cryptominisat5/solvertypesmini.h>
#include <cstdint>
#include <random>
#include <vector>

namespace ArjunNS::fuzz {

// General random AIG: mixed AND/OR/NOT/ITE/XOR ops over a literal pool.
inline aig_ptr gen_random_aig(ArjunNS::AIGManager& aig_mng,
                              std::mt19937& rng, uint32_t num_vars,
                              uint32_t depth, uint32_t max_nodes)
{
    std::vector<aig_ptr> pool;
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.push_back(AIG::new_lit(v, false));
        pool.push_back(AIG::new_lit(v, true));
    }
    if (rng() % 8 == 0) pool.push_back(aig_mng.new_const(true));
    if (rng() % 8 == 0) pool.push_back(aig_mng.new_const(false));

    uint32_t nodes_built = 0;
    for (uint32_t d = 0; d < depth && nodes_built < max_nodes; d++) {
        uint32_t new_this_level = 1 + rng() % 4;
        for (uint32_t i = 0; i < new_this_level && nodes_built < max_nodes; i++) {
            if (pool.size() < 2) break;
            auto pick = [&]() -> uint32_t {
                if (rng() % 3 == 0) return rng() % pool.size();
                uint32_t lo = pool.size() > 4 ? pool.size() - pool.size() / 2 : 0;
                return lo + rng() % (pool.size() - lo);
            };
            uint32_t idx_a = pick();
            uint32_t idx_b = pick();
            if (idx_a == idx_b) idx_b = (idx_b + 1) % pool.size();
            aig_ptr a = pool[idx_a];
            aig_ptr b = pool[idx_b];
            uint32_t op = rng() % 7;
            aig_ptr node;
            switch (op) {
                case 0: node = AIG::new_and(a, b, false); break;
                case 1: node = AIG::new_and(a, b, true); break;
                case 2: node = AIG::new_or(a, b, false); break;
                case 3: node = AIG::new_or(a, b, true); break;
                case 4: node = AIG::new_not(a); break;
                case 5: {
                    uint32_t bvar = rng() % num_vars;
                    bool bneg = rng() % 2;
                    node = AIG::new_ite(a, b, CMSat::Lit(bvar, bneg));
                    break;
                }
                case 6: {
                    // XOR
                    node = AIG::new_or(
                        AIG::new_and(a, AIG::new_not(b)),
                        AIG::new_and(AIG::new_not(a), b));
                    break;
                }
            }
            pool.push_back(node);
            nodes_built++;
        }
    }
    if (pool.size() <= num_vars * 2) return pool[rng() % pool.size()];
    uint32_t start = pool.size() * 2 / 3;
    return pool[start + rng() % (pool.size() - start)];
}

// Manthan-style: nested ITE trees whose selectors are ANDs of many literals.
// Exponential in depth — caller must pick tiny depth (2..6). Doesn't use
// AIGManager directly but takes one so every generator has the same signature.
inline aig_ptr gen_manthan_aig(ArjunNS::AIGManager& aig_mng,
                               std::mt19937& rng, uint32_t num_vars,
                               uint32_t depth, uint32_t max_branch_width)
{
    if (depth == 0) {
        uint32_t pick = rng() % 10;
        if (pick == 0) return aig_mng.new_const(true);
        if (pick == 1) return aig_mng.new_const(false);
        return AIG::new_lit(rng() % num_vars, rng() % 2);
    }
    uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
    if (rng() % 3 == 0) k = std::max<uint32_t>(k, 3u + rng() % std::max<uint32_t>(1u, max_branch_width));
    aig_ptr branch = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t i = 1; i < k; i++) {
        branch = AIG::new_and(branch, AIG::new_lit(rng() % num_vars, rng() % 2));
    }
    if (rng() % 5 == 0) branch = AIG::new_not(branch);
    aig_ptr then_arm = gen_manthan_aig(aig_mng, rng, num_vars, depth - 1, max_branch_width);
    aig_ptr else_arm = gen_manthan_aig(aig_mng, rng, num_vars, depth - 1, max_branch_width);
    return AIG::new_or(AIG::new_and(branch, then_arm),
                       AIG::new_and(AIG::new_not(branch), else_arm));
}

// Deep linear ITE chain. Models manthan's repair loop: each iteration adds
// one ITE on top of the growing formula. Linear in chain_depth.
inline aig_ptr gen_deep_ite_chain_aig(ArjunNS::AIGManager& /*aig_mng*/,
                                      std::mt19937& rng, uint32_t num_vars,
                                      uint32_t chain_depth,
                                      uint32_t max_branch_width)
{
    aig_ptr f = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t step = 0; step < chain_depth; step++) {
        uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
        if (rng() % 4 == 0) k = std::max<uint32_t>(k, max_branch_width);
        aig_ptr branch = AIG::new_lit(rng() % num_vars, rng() % 2);
        for (uint32_t i = 1; i < k; i++) {
            branch = AIG::new_and(branch, AIG::new_lit(rng() % num_vars, rng() % 2));
        }
        aig_ptr repair;
        if (rng() % 5 == 0) {
            repair = AIG::new_and(
                AIG::new_lit(rng() % num_vars, rng() % 2),
                AIG::new_lit(rng() % num_vars, rng() % 2));
        } else {
            repair = AIG::new_lit(rng() % num_vars, rng() % 2);
        }
        f = AIG::new_or(AIG::new_and(branch, repair),
                        AIG::new_and(AIG::new_not(branch), f));
    }
    return f;
}

// OR of several (AND of literals). Models the DNF-cover loop in manthan.cpp.
inline aig_ptr gen_dnf_cover_aig(ArjunNS::AIGManager& aig_mng,
                                 std::mt19937& rng, uint32_t num_vars,
                                 uint32_t num_branches, uint32_t max_branch_width)
{
    aig_ptr overall = nullptr;
    for (uint32_t b = 0; b < num_branches; b++) {
        uint32_t k = 1 + rng() % std::max<uint32_t>(1u, max_branch_width);
        aig_ptr cur = AIG::new_lit(rng() % num_vars, rng() % 2);
        for (uint32_t i = 1; i < k; i++) {
            cur = AIG::new_and(cur, AIG::new_lit(rng() % num_vars, rng() % 2));
        }
        overall = overall ? AIG::new_or(overall, cur) : cur;
    }
    if (overall == nullptr) overall = aig_mng.new_const(true);
    if (rng() % 3 == 0) overall = AIG::new_not(overall);
    return overall;
}

// Pure big-AND of distinct literals. Canonical target for k-ary AND fusion.
// Uses each var at most once (one polarity) to avoid complementary fold to FALSE.
inline aig_ptr gen_pure_and_chain(ArjunNS::AIGManager& /*aig_mng*/,
                                  std::mt19937& rng, uint32_t num_vars, uint32_t len)
{
    if (len < 2) len = 2;
    std::vector<std::pair<uint32_t, bool>> pool;
    pool.reserve(2 * num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.emplace_back(v, false);
        pool.emplace_back(v, true);
    }
    std::shuffle(pool.begin(), pool.end(), rng);
    uint32_t actual = std::min<uint32_t>(len, pool.size());
    if (actual < 2) actual = std::min<uint32_t>(2u, pool.size());
    std::vector<char> used(num_vars, 0);
    aig_ptr cur = nullptr;
    uint32_t made = 0;
    for (auto& p : pool) {
        if (used[p.first]) continue;
        used[p.first] = 1;
        aig_ptr lit = AIG::new_lit(p.first, p.second);
        cur = cur ? AIG::new_and(cur, lit) : lit;
        if (++made >= actual) break;
    }
    if (!cur) cur = AIG::new_lit(0, false);
    if (rng() % 5 == 0) cur = AIG::new_not(cur);
    return cur;
}

inline aig_ptr gen_pure_or_chain(ArjunNS::AIGManager& /*aig_mng*/,
                                 std::mt19937& rng, uint32_t num_vars, uint32_t len)
{
    if (len < 2) len = 2;
    std::vector<std::pair<uint32_t, bool>> pool;
    pool.reserve(2 * num_vars);
    for (uint32_t v = 0; v < num_vars; v++) {
        pool.emplace_back(v, false);
        pool.emplace_back(v, true);
    }
    std::shuffle(pool.begin(), pool.end(), rng);
    uint32_t actual = std::min<uint32_t>(len, pool.size());
    if (actual < 2) actual = std::min<uint32_t>(2u, pool.size());
    std::vector<char> used(num_vars, 0);
    aig_ptr cur = nullptr;
    uint32_t made = 0;
    for (auto& p : pool) {
        if (used[p.first]) continue;
        used[p.first] = 1;
        aig_ptr lit = AIG::new_lit(p.first, p.second);
        cur = cur ? AIG::new_or(cur, lit) : lit;
        if (++made >= actual) break;
    }
    if (!cur) cur = AIG::new_lit(0, false);
    if (rng() % 5 == 0) cur = AIG::new_not(cur);
    return cur;
}

// Balanced-tree big-AND / big-OR: pairwise bottom-up. log2(len) deep but
// k-ary semantics. Exercises the encoder's flattening through internal
// fanout-1 AND nodes.
inline aig_ptr gen_balanced_and_tree(ArjunNS::AIGManager& /*aig_mng*/,
                                     std::mt19937& rng, uint32_t num_vars, uint32_t len)
{
    if (len < 2) len = 2;
    std::vector<aig_ptr> level;
    level.reserve(len);
    for (uint32_t i = 0; i < len; i++) {
        level.push_back(AIG::new_lit(rng() % num_vars, rng() % 2));
    }
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_and(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

inline aig_ptr gen_balanced_or_tree(ArjunNS::AIGManager& /*aig_mng*/,
                                    std::mt19937& rng, uint32_t num_vars, uint32_t len)
{
    if (len < 2) len = 2;
    std::vector<aig_ptr> level;
    level.reserve(len);
    for (uint32_t i = 0; i < len; i++) {
        level.push_back(AIG::new_lit(rng() % num_vars, rng() % 2));
    }
    while (level.size() > 1) {
        std::vector<aig_ptr> next;
        for (size_t i = 0; i + 1 < level.size(); i += 2) {
            next.push_back(AIG::new_or(level[i], level[i+1]));
        }
        if (level.size() % 2 == 1) next.push_back(level.back());
        level = std::move(next);
    }
    return level[0];
}

// Arbitrary deep chain of mixed AND/OR with a literal threaded through.
inline aig_ptr gen_chain_aig(ArjunNS::AIGManager& /*aig_mng*/,
                             std::mt19937& rng, uint32_t num_vars, uint32_t chain_len)
{
    aig_ptr chain = AIG::new_lit(rng() % num_vars, rng() % 2);
    for (uint32_t i = 0; i < chain_len; i++) {
        aig_ptr leaf = AIG::new_lit(rng() % num_vars, rng() % 2);
        switch (rng() % 4) {
            case 0: chain = AIG::new_and(chain, leaf); break;
            case 1: chain = AIG::new_or(chain, leaf); break;
            case 2: chain = AIG::new_and(leaf, chain); break;
            case 3: chain = AIG::new_or(leaf, chain); break;
        }
    }
    if (rng() % 3 == 0) chain = AIG::new_not(chain);
    if (rng() % 4 == 0) {
        aig_ptr other = AIG::new_lit(rng() % num_vars, rng() % 2);
        chain = AIG::new_ite(chain, other, CMSat::Lit(rng() % num_vars, rng() % 2));
    }
    return chain;
}

// Shape codes returned by pick_shape. The selection weights here are the
// same ones the aig_to_cnf fuzzer has always used, mirroring the relative
// frequency of each pattern in the real manthan / arjun workload.
enum class Shape : uint8_t {
    DeepIteChain,
    DnfCover,
    Manthan,
    Random,
    Chain,
    PureAndChain,
    PureOrChain,
    BalancedAndTree,
    BalancedOrTree,
};

inline Shape pick_shape(std::mt19937& rng) {
    uint32_t s = rng() % 16;
    if (s < 4)  return Shape::DeepIteChain;
    if (s < 6)  return Shape::DnfCover;
    if (s < 7)  return Shape::Manthan;
    if (s < 8)  return Shape::Random;
    if (s < 9)  return Shape::Chain;
    if (s < 11) return Shape::PureAndChain;
    if (s < 13) return Shape::PureOrChain;
    if (s < 14) return Shape::BalancedAndTree;
    return Shape::BalancedOrTree;
}

// Emit a random AIG whose shape is picked by pick_shape(). max_vars, max_depth
// and max_nodes are the same knobs the existing fuzzer uses.
inline aig_ptr gen_random_shape(ArjunNS::AIGManager& aig_mng,
                                std::mt19937& rng,
                                uint32_t num_vars, uint32_t depth, uint32_t max_nodes)
{
    Shape sh = pick_shape(rng);
    switch (sh) {
        case Shape::DeepIteChain: {
            uint32_t d = 50 + rng() % 450;
            if (rng() % 20 == 0) d = 500 + rng() % 500;
            uint32_t bw = 2 + rng() % 8;
            return gen_deep_ite_chain_aig(aig_mng, rng, num_vars, d, bw);
        }
        case Shape::DnfCover: {
            uint32_t nb = 2 + rng() % 8;
            uint32_t bw = 2 + rng() % 6;
            return gen_dnf_cover_aig(aig_mng, rng, num_vars, nb, bw);
        }
        case Shape::Manthan: {
            uint32_t d = 2 + rng() % 4;
            uint32_t bw = 2 + rng() % 6;
            return gen_manthan_aig(aig_mng, rng, num_vars, d, bw);
        }
        case Shape::Random:
            return gen_random_aig(aig_mng, rng, num_vars, depth, max_nodes);
        case Shape::Chain:
            return gen_chain_aig(aig_mng, rng, num_vars, 5 + rng() % 25);
        case Shape::PureAndChain:
            return gen_pure_and_chain(aig_mng, rng, num_vars, 10 + rng() % 790);
        case Shape::PureOrChain:
            return gen_pure_or_chain(aig_mng, rng, num_vars, 10 + rng() % 790);
        case Shape::BalancedAndTree:
            return gen_balanced_and_tree(aig_mng, rng, num_vars, 8 + rng() % 500);
        case Shape::BalancedOrTree:
            return gen_balanced_or_tree(aig_mng, rng, num_vars, 8 + rng() % 500);
    }
    return aig_mng.new_const(true);
}

} // namespace ArjunNS::fuzz
