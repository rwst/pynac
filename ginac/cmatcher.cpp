// cmatcher.cpp: commutative matching
// Distributed under GPL2+
// Author: 2018: Ralf Stephan <ralf@ark.in-berlin.de>
//
// This differs from basic::match() because commutative structures
// need a special algorithm. We follow the outline in
// Manuel Krebber's Master Thesis, "Non-linear Associative-Commutative
// Many-to-One Pattern Matching with Sequence Variables", section 3.2
// https://arxiv.org/abs/1705.00907
//
// TODO:
//       - one "global wildcard" (see basic::match)
//       - zero wildcards (matching superfluous wilds with 0(+) or 1(*)
//       - constant wildcards (not having specified symbols)
//       - more than one global wildcard
//       - more than two args with noncommutative functions
//       - commutative functions

#include "cmatcher.h"
#include "expairseq.h"
#include "wildcard.h"
#include "operators.h"
#include "utils.h"

#include <iostream>
#include <algorithm>

#define DEBUG if(debug)

namespace GiNaC {

static bool debug=false;

void CMatcher::init()
{
        DEBUG std::cerr<<"cmatch: "<<source<<", "<<pattern<<", "<<map<<std::endl; 
	if (is_exactly_a<wildcard>(pattern)) {
                const auto& it = map.find(pattern);
                if (it != map.end()) {
		        if (not source.is_equal(ex_to<basic>(it->second))) {
                                ret_val = false;
                                return;
                        }
                        ret_val = true;
                        ret_map = map;
                        return;
                }
		map[pattern] = source;
                ret_val = true;
                ret_map = map;
		return;
	} 
	if (ex_to<basic>(source).tinfo() != ex_to<basic>(pattern).tinfo()) {
                ret_val = false;
                return;
        }
        size_t nops = source.nops();
        if (nops != pattern.nops()) {
                ret_val = false;
                return;
        }

        // Chop into terms
        exvector wilds;
        for (size_t i=0; i<nops; i++) {
                ops.push_back(source.op(i));
        }
        for (size_t i=0; i<pattern.nops(); i++) {
                if (is_exactly_a<wildcard>(pattern.op(i)))
                        wilds.push_back(pattern.op(i));
                else {
                        pat.push_back(pattern.op(i));
                }
        }

        // First, match all terms without unset wildcards from the pattern
        // If there are matches remove them from both subject and pattern
        for (auto it1 = wilds.begin(); it1 != wilds.end(); ) {
                const auto& mit = map.find(*it1);
                if (mit == map.end()) {
                        ++it1;
                        continue;
                }
                bool matched = false;
                for (auto it2 = ops.begin(); it2 != ops.end(); ++it2) {
                        if (it2->is_equal(mit->second)) {
                                (void)ops.erase(it2);
                                matched = true;
                                break;
                        }
                }
                if (matched) {
                        it1 = wilds.erase(it1);
                        DEBUG std::cerr<<"preset "<<mit->first<<" == "<<mit->second<<" found in "<<source<<std::endl;
                }
                else
                        ++it1;
        }
        // Check that all "constants" in the pattern are matched
        for (auto it1 = pat.begin(); it1 != pat.end(); ) {
                if (haswild(*it1)) {
                        ++it1;
                        continue;
                }
                bool matched = false;
                for (auto it2 = ops.begin(); it2 != ops.end(); ) {
                        if (it2->is_equal(*it1)) {
                                (void)ops.erase(it2);
                                matched = true;
                                break;
                        }
                        ++it2;
                }
                if (not matched) {
                        DEBUG std::cerr<<"constant "<<*it1<<" not found in "<<source<<std::endl;
                        ret_val = false;
                        return;
                }
                        DEBUG std::cerr<<"constant "<<*it1<<" found in "<<source<<std::endl;
                it1 = pat.erase(it1);
        }
        if (wilds.empty() and ops.empty() and pat.empty()) {
                ret_val = true;
                ret_map = map;
                return;
        }
        if (wilds.empty() and (ops.empty() or pat.empty()))
                throw std::runtime_error("matching gotcha");

        for (auto&& w : wilds)
                pat.insert(pat.begin(), w);

        N = pat.size();
        std::optional<CMatcher> ocm;
        for (size_t i=0; i<N; ++i) {
                perm.push_back(i);
                cms.push_back(ocm);
        }
        all_perms = false;
}

void CMatcher::run()
{
        if (all_perms or perm.empty()) {
                ret_val = false;
                return;
        }
        DEBUG std::cerr<<"run() entered"<<std::endl;
        clear_ret();
        std::vector<exmap> map_repo(N);
        // The outer loop goes though permutations of perm
        while (true) {
                size_t index = 0;
                bool perm_failed = false;
                std::vector<bool> pterm_matched(N);
                pterm_matched.assign(N, false);
                DEBUG { std::cerr<<"["; for (size_t i:perm) std::cerr<<i<<","; std::cerr<<"]"<<std::endl; }
                // The second loop increases index to get a new ops term
                do {
                        const ex& e = ops[perm[index]];
                        DEBUG std::cerr<<"index: "<<index<<", e: "<<e<<std::endl;
                        if (index == 0)
                                map_repo[0] = map;
                        else
                                map_repo[index] = map_repo[index-1];
                        bool pterm_found = false;
                        for (size_t i=0; i<pat.size(); ++i) {
                                if (pterm_matched[i])
                                        continue;
                                // At this point we try matching p to e 
                                const ex& p = pat[i];
                                exmap m = map_repo[index];
                                if (cms[index])
                                        cms[index].reset();
                                if (not is_a<expairseq>(p)
                                    or not is_a<expairseq>(e)) {
                                        // normal matching attempt
                                        bool ret = e.match(p, m);
                                        if (ret) {
                                                map_repo[index] = m;
                                                pterm_matched[i] = true;
                                                pterm_found = true;
                                                DEBUG std::cerr<<"match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                                break;
                                        }
                                }
                                else {
                                        // both p and e are sum or product
                                        cms[index].emplace(CMatcher(e, p, m));
                                        CMatcher& cm = cms[index].value();
                                        std::optional<exmap> opm = cm.get();
                                        if (opm) {
                                                map_repo[index] = opm.value();
                                                pterm_matched[i] = true;
                                                pterm_found = true;
                                                DEBUG std::cerr<<"cmatch found: "<<e<<", "<<p<<", "<<map_repo[index]<<std::endl;
                                                break;
                                        }
                                        else {
                                                cms[index].reset();
                                        }
                                }
                                if (pterm_found)
                                        break;
                        }
                        if (not pterm_found) {
                        // did we start coroutines in this permutation?
                                bool alt_solution_found = false;
                                int i = static_cast<int>(index);
                                while (--i >= 0) {
                                        if (cms[i]) {
                                                CMatcher& cm = cms[i].value();
                                                DEBUG std::cerr<<"find alt: "<<i<<std::endl;
                                                cm.clear_ret();
                                                std::optional<exmap> opm = cm.get();
                                                if (opm) {
                                                        map_repo[i] = opm.value();
                                                        index = i;
                                                        alt_solution_found = true;
                                                        DEBUG std::cerr<<"try alt: "<<i<<", "<<map_repo[i]<<std::endl;
                                                        break;
                                                }
                                                cms[i].reset();
                                        }
                                }
                                if (not alt_solution_found) {
                                        perm_failed = true;
                                        break;
                                }
                        }
                }
                while (++index < N);

                if (not perm_failed) {
                        // permute and get leftmost changed position
                        int pos = next_permutation_pos(perm.begin(),
                                        perm.end());
                        if (pos < 0) {
                                all_perms = true;
                        }
                        // give back one solution of this cmatch call
                        // still permutations left
                        // state could save index too
                        index = pos;
                        DEBUG std::cerr<<"send alt: "<<map_repo[N-1]<<std::endl;
                        ret_val = true;
                        ret_map = map_repo[N-1];
                        return;
                }
                else {
                        // no cmatch calls have alternative solutions
                        // to their cmatch, so get the next permutation
                        // that changes current index position
                        size_t old = perm[index];
                        while (perm[index] == old) {
                                bool more = std::next_permutation(perm.begin(),
                                                perm.end());
                                if (not more) {
                                        ret_val = false;
                                        DEBUG std::cerr<<"perms exhausted"<<std::endl;
                                        return;
                                }
                        }
                }
        }
        DEBUG std::cerr<<"run() exited"<<std::endl;
        ret_val = false;
}

}
