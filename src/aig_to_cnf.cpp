/*
 Arjun - Efficient AIG to CNF Conversion

 The encoder is a header-only template (see aig_to_cnf.h). This TU only
 houses the non-template statistics printer.

 Copyright (c) 2020, Mate Soos. MIT License.
 */

#include "aig_to_cnf.h"
#include <iomanip>
#include <iostream>

namespace ArjunNS {

void AIG2CNFStats::print(int verb) const {
    if (verb <= 0) return;
    std::cout
        << "c [aig2cnf] nodes=" << nodes_visited
        << " helpers=" << helpers_added
        << " clauses=" << clauses_added
        << " hits=" << cache_hits
        << "\n"
        << "c [aig2cnf] kAND: " << kary_and_count
        << " (avg-width " << std::fixed << std::setprecision(2)
        << (kary_and_count ? (double)kary_and_width_total / kary_and_count : 0.0)
        << ")  kOR: " << kary_or_count
        << " (avg-width "
        << (kary_or_count ? (double)kary_or_width_total / kary_or_count : 0.0)
        << ")  ITE: " << ite_patterns
        << "  MUX3: " << mux3_patterns
        << "  XOR: " << xor_patterns
        << "  CUT: " << cut_cnf_patterns << "/" << cut_cnf_clauses << "cls"
        << std::endl;
}

} // namespace ArjunNS
