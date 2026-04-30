/*
 Arjun - Minimum-clause CNF encoding for small truth tables.

 Given the truth table of a k-input Boolean function f (k ≤ 4), compute the
 minimum-clause CNF encoding of `g ↔ f(x₀, …, x_{k-1})`.

 This backs the cut-based CNF path in AIGToCNF: once a subtree is
 characterised by a (leaves, tt) pair, the minimum clause set for `g ↔ f`
 replaces whatever pairwise/Tseitin clauses the pattern path would emit.

 Minimum CNF for g ↔ f splits into:
   • Clauses enforcing g → f: one clause per prime-implicant cover of the
     on-set of f. Each prime π becomes `(¬x_i)_{for x_i set in π} ∨ g ...` —
     but here we want CNF, so we translate differently: each prime implicant
     of ¬f becomes a clause of g (covers off-minterms).
   • Clauses enforcing f → g: each prime implicant of f becomes a clause of
     ¬g (covers on-minterms).

 The minimum-cover-of-primes problem is NP-hard in general; for k ≤ 4 we
 solve it exactly by brute force over subsets.

 Implemented as a header-only cache keyed on (num_inputs, tt). The cache is
 populated lazily and is thread-safe under `std::call_once` if the caller
 needs concurrency — the current AIGToCNF is single-threaded per encoder so
 we keep it lock-free.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#pragma once

#include <cassert>
#include <cstdint>
#include <unordered_map>
#include <vector>

namespace ArjunNS::cut_cnf {

// A clause is encoded as two bit-masks over k ≤ 4 inputs:
//   present[i] = 1 iff input i appears in the clause
//   sign[i]    = 1 iff input i appears negated in the clause
// Plus a "g sign": 0 → clause contains +g, 1 → clause contains ¬g.
struct Clause {
    uint8_t present; // bit i: x_i present
    uint8_t sign;    // bit i: x_i appears negated (requires present[i]=1)
    uint8_t g_sign;  // 0 → g, 1 → ¬g
};

struct MinCnf {
    std::vector<Clause> clauses;
    uint32_t num_inputs = 0;
};

// ---------------------------------------------------------------------------
// Quine-McCluskey: find all prime implicants of the boolean function whose
// on-minterms are the 1-bits of `on_mask`. Implicants are encoded as
// (value, dontcare): for input i,
//   dontcare bit i = 1 → input irrelevant in this implicant
//   value bit i    = literal value if not dontcare
// num_inputs determines the minterm-space size (1 << num_inputs).
// ---------------------------------------------------------------------------

struct Implicant {
    uint8_t value;
    uint8_t dontcare;
    // Bitset of minterms covered. For k ≤ 4 this fits in a uint16_t.
    uint16_t covers;
};

inline uint16_t implicant_covers(uint8_t value, uint8_t dontcare,
                                 uint32_t num_inputs) {
    uint16_t res = 0;
    uint16_t max_m = 1u << num_inputs;
    uint8_t care_mask = ((1u << num_inputs) - 1) & (uint8_t)~dontcare;
    uint8_t core = value & care_mask;
    for (uint16_t m = 0; m < max_m; m++) {
        if ((m & care_mask) == core) res |= (uint16_t)(1u << m);
    }
    return res;
}

// Count population. __builtin_popcount is more portable but std::popcount
// requires C++20 -- we're on -std=c++23 so either works.
inline uint32_t popcount16(uint16_t x) { return __builtin_popcount(x); }

inline std::vector<Implicant> prime_implicants(uint16_t on_mask,
                                               uint32_t num_inputs) {
    // Group implicants by the number of 1-bits in their `value & ~dontcare`.
    // Start with single-minterm implicants.
    uint16_t max_m = 1u << num_inputs;
    std::vector<Implicant> current;
    for (uint16_t m = 0; m < max_m; m++) {
        if (on_mask & (1u << m)) {
            Implicant im{ (uint8_t)m, 0, (uint16_t)(1u << m) };
            current.push_back(im);
        }
    }
    std::vector<Implicant> primes;
    while (!current.empty()) {
        std::vector<bool> used(current.size(), false);
        std::vector<Implicant> next;
        // Try to merge each pair whose dontcare masks match and whose values
        // differ in exactly one bit.
        for (size_t i = 0; i < current.size(); i++) {
            for (size_t j = i + 1; j < current.size(); j++) {
                if (current[i].dontcare != current[j].dontcare) continue;
                uint8_t dc = current[i].dontcare;
                uint8_t care_mask = ((1u << num_inputs) - 1) & (uint8_t)~dc;
                uint8_t diff = (current[i].value ^ current[j].value) & care_mask;
                if (popcount16(diff) != 1) continue;
                Implicant merged;
                merged.dontcare = dc | diff;
                merged.value = current[i].value & (uint8_t)~diff;
                merged.covers = current[i].covers | current[j].covers;
                // Dedup against already-added merges.
                bool dup = false;
                for (const auto& e : next) {
                    if (e.value == merged.value && e.dontcare == merged.dontcare) {
                        dup = true; break;
                    }
                }
                if (!dup) next.push_back(merged);
                used[i] = true;
                used[j] = true;
            }
        }
        // Anything unmerged in this round is a prime.
        for (size_t i = 0; i < current.size(); i++) {
            if (!used[i]) {
                bool dup = false;
                for (const auto& p : primes) {
                    if (p.value == current[i].value
                        && p.dontcare == current[i].dontcare) { dup = true; break; }
                }
                if (!dup) primes.push_back(current[i]);
            }
        }
        current = std::move(next);
    }
    return primes;
}

// Exact min-cover of `target_minterms` using primes. For k ≤ 4 there are at
// most 16 minterms and typically ≤ 16 primes; brute force over subsets is
// fine.
inline std::vector<Implicant> min_cover(const std::vector<Implicant>& primes,
                                        uint16_t target_minterms)
{
    if (target_minterms == 0) return {};
    // Bounded by the number of primes. For k=4 worst case ~18 primes; 2^18
    // enumeration is 260k. Cache keeps us from redoing it.
    size_t n = primes.size();
    assert(n <= 24 && "too many primes for brute force");
    std::vector<Implicant> best;
    size_t best_size = n + 1;
    for (size_t s = 0; s < (size_t(1) << n); s++) {
        if ((size_t)__builtin_popcountll((uint64_t)s) >= best_size) continue;
        uint16_t cov = 0;
        for (size_t i = 0; i < n; i++) {
            if (s & (size_t(1) << i)) cov |= primes[i].covers;
        }
        if ((cov & target_minterms) != target_minterms) continue;
        std::vector<Implicant> pick;
        for (size_t i = 0; i < n; i++) {
            if (s & (size_t(1) << i)) pick.push_back(primes[i]);
        }
        if (pick.size() < best_size) {
            best_size = pick.size();
            best = std::move(pick);
        }
    }
    return best;
}

inline MinCnf compute_min_cnf(uint32_t num_inputs, uint32_t tt) {
    assert(num_inputs >= 1 && num_inputs <= 4);
    uint32_t max_m = 1u << num_inputs;
    uint32_t full_mask = (1u << max_m) - 1;
    uint16_t on_mask  = (uint16_t)(tt & full_mask);
    uint16_t off_mask = (uint16_t)(~tt & full_mask);

    MinCnf out;
    out.num_inputs = num_inputs;

    // Degenerate: f is constant. One unit clause fixes g.
    if (on_mask == 0)  { out.clauses.push_back({0, 0, 1}); return out; }
    if (off_mask == 0) { out.clauses.push_back({0, 0, 0}); return out; }

    // Clauses enforcing (f → g): each prime implicant of the on-set covers a
    // region of on-minterms and becomes a g-clause (¬cube ∨ g).
    auto primes_on = prime_implicants(on_mask, num_inputs);
    auto cover_on  = min_cover(primes_on, on_mask);
    for (const auto& p : cover_on) {
        Clause c;
        uint8_t care = ((1u << num_inputs) - 1) & (uint8_t)~p.dontcare;
        c.present = care;
        // In the clause, a literal x_i is negated iff x_i = 1 in the cube.
        c.sign = p.value & care;
        c.g_sign = 0;
        out.clauses.push_back(c);
    }

    // Clauses enforcing (g → f): primes of the off-set → ¬g-clauses.
    auto primes_off = prime_implicants(off_mask, num_inputs);
    auto cover_off  = min_cover(primes_off, off_mask);
    for (const auto& p : cover_off) {
        Clause c;
        uint8_t care = ((1u << num_inputs) - 1) & (uint8_t)~p.dontcare;
        c.present = care;
        c.sign = p.value & care;
        c.g_sign = 1;
        out.clauses.push_back(c);
    }

    return out;
}

// Cache lookup. Key: (num_inputs << 16) | tt_bits.
//
// Output-polarity canonicalisation: in the input-edge-neg AIG model the
// referring edge's sign is free, so f and ~f share one canonical CNF entry.
// We key the underlying compute on min(tt, ~tt & full_mask); the complement
// is derived by flipping g_sign on every clause. For 4-input cuts this
// halves the table (up to 64K TTs → 32K canonical entries) without changing
// any observable encoder output.
inline const MinCnf& min_cnf_for_tt(uint32_t num_inputs, uint32_t tt) {
    static std::unordered_map<uint32_t, MinCnf> cache;
    const uint32_t max_m = 1u << num_inputs;
    const uint32_t full_mask = (1u << max_m) - 1;
    const uint32_t tt_bits = tt & full_mask;
    const uint32_t key = (num_inputs << 16) | tt_bits;

    auto it = cache.find(key);
    if (it != cache.end()) return it->second;

    const uint32_t tt_compl = full_mask & ~tt_bits;
    const uint32_t canon_tt = (tt_bits <= tt_compl) ? tt_bits : tt_compl;
    const uint32_t canon_key = (num_inputs << 16) | canon_tt;

    // Ensure the canonical entry is cached. std::unordered_map keeps
    // references to mapped values stable across rehashes (only iterators
    // may invalidate), so any reference we hold into `cache` remains valid
    // across further emplaces.
    auto cit = cache.find(canon_key);
    if (cit == cache.end()) {
        MinCnf computed = compute_min_cnf(num_inputs, canon_tt);
        auto [ins, _] = cache.emplace(canon_key, std::move(computed));
        cit = ins;
    }

    // If tt was already canonical, we're done.
    if (canon_tt == tt_bits) return cit->second;

    // Otherwise derive the complement form by flipping every clause's g_sign.
    MinCnf flipped = cit->second;
    for (auto& c : flipped.clauses) c.g_sign ^= 1;
    auto [ins, _] = cache.emplace(key, std::move(flipped));
    return ins->second;
}

} // namespace ArjunNS::cut_cnf
