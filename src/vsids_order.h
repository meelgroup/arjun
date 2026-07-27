#pragma once

#include <cstdint>
#include <vector>
#include <algorithm>

namespace ArjunInt {

// VSIDS-style activity for CEGAR variable ordering. Each conflict bumps its
// participating y-vars by var_inc, then var_inc grows by 1/decay. High activity
// => demote late in reorder_vars. decay tightens toward 1 across restarts so the
// order stabilises over time. The whole object is carried across restart rounds.
class VsidsOrder {
public:
    void init(const uint32_t nvars) {
        if (activity.size() < nvars) activity.resize(nvars, 0.0);
    }
    void set_decay(const double d) { one_minus_decay = 1.0 - d; }
    void set_shrink(const double s) { shrink = s; }

    void bump(const uint32_t v) {
        if ((activity[v] += var_inc) > rescale_limit) rescale();
    }
    // Once per conflict, after bumping its vars.
    void decay_step() {
        var_inc /= (1.0 - one_minus_decay);
        if (var_inc > rescale_limit) rescale();
    }
    // Tighten decay toward 1 for the next restart round.
    void on_restart() {
        one_minus_decay = std::max(min_one_minus_decay, one_minus_decay * shrink);
    }
    double get(const uint32_t v) const { return activity[v]; }
    double decay() const { return 1.0 - one_minus_decay; }

private:
    void rescale() {
        for (auto& a : activity) a *= 1e-100;
        var_inc *= 1e-100;
    }
    std::vector<double> activity;
    double var_inc = 1.0;
    double one_minus_decay = 0.01;      // decay = 0.99
    double shrink = 0.5;                // per restart: (1-decay) *= shrink
    double min_one_minus_decay = 1e-4;  // decay ceiling 0.9999
    static constexpr double rescale_limit = 1e100;
};

}
