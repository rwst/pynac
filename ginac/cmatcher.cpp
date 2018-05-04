// cmatcher.cpp: commutative matching
// Distributed under GPL2+
// Author: 2018: Ralf Stephan <ralf@ark.in-berlin.de>
//
// This differs from GiNaC's original basic::match() because commutative
// structures need a special algorithm. We follow the outline in
// Manuel Krebber's Master Thesis, "Non-linear Associative-Commutative
// Many-to-One Pattern Matching with Sequence Variables", section 3.2
// https://arxiv.org/abs/1705.00907
//
// Features:
//       - commutative matching (sums and products, backtracking also in
//         powers and functions with two arguments)
//
// TODO:
//       - one "global wildcard" (i.e. x^+ in a f_C, see basic::match)
//       - "zero wildcards" (matching superfluous wilds with 0(+) or 1(*)
//       - constant wildcards (those lacking specified symbols)
//       - more than two args with noncommutative functions
//       - commutative functions
//       - more than one global wildcard (i.e., fully seqential)

#include "cmatcher.h"
#include "expairseq.h"
#include "symbol.h"
#include "wildcard.h"
#include "power.h"
#include "function.h"
#include "operators.h"
#include "utils.h"

#include <iostream>
#include <algorithm>

#define DEBUG if(debug)

namespace GiNaC {

static bool debug=true;
int CMatcher::level = 0;

void CMatcher::init()
{
        DEBUG std::cerr<<level<<" cmatch: "<<source<<", "<<pattern<<", "<<map<<std::endl;
        const size_t snops = source.nops(), pnops = pattern.nops();
	if (is_exactly_a<wildcard>(pattern)) {
                DEBUG std::cerr << "pattern is single wildcard"<<std::endl;
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
                DEBUG std::cerr<<"pattern type mismatch"<<std::endl;
                ret_val = false;
                return;
        }
        if (snops < pnops) {
                DEBUG std::cerr<<"# of source terms > pattern terms"<<std::endl;
                ret_val = false;
                return;
        }
        symbolset oset = source.symbols();
        symbolset pset = substitute(pattern.wilds(), map);
        if (not subset_of(pset, oset)) {
                DEBUG std::cerr<<"substitution has unmatched symbols"<<std::endl;
                ret_val = false;
                return;
        }

        // Chop into terms
        exvector wilds;
        for (size_t i=0; i<snops; i++) {
                ops.push_back(source.op(i));
        }
        for (size_t i=0; i<pnops; i++) {
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
                        DEBUG std::cerr<<level<<" preset "<<mit->first<<" == "<<mit->second<<" found in "<<source<<std::endl;
                }
                else {
                        DEBUG std::cerr<<level<<" preset "<<mit->first<<" == "<<mit->second<<" conflict, "<<mit->second<<" not found"<<std::endl;
                        ret_val = false;
                        return;
                }
        }
        if (snops > pnops) {
                if (wilds.empty()) {
                        ret_val = false;
                        return;
                }
                // we have a global wildcard, i.e., one that matches
                // more than one term (x^+ in the paper) in a sum or
                // product
                global_wild = true;
                DEBUG std::cerr<<"global wildcard seen: "<<snops<<","<<pnops<<std::endl;
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
                        DEBUG std::cerr<<level<<" constant "<<*it1<<" not found in "<<source<<std::endl;
                        ret_val = false;
                        return;
                }
                        DEBUG std::cerr<<level<<" constant "<<*it1<<" found in "<<source<<std::endl;
                it1 = pat.erase(it1);
        }
        if (wilds.empty() and ops.empty() and pat.empty()) {
                ret_val = true;
                ret_map = map;
                return;
        }
        if (wilds.empty() and (ops.empty() or pat.empty()))
                throw std::runtime_error("matching gotcha");

        if (is_exactly_a<power>(source)) {
                if (wilds.empty() and pat.empty())
                        throw std::runtime_error("matching gotcha");
                std::optional<CMatcher> ocm;
                cms.push_back(ocm);
                if (ops.size() == 2) {
                        cms.push_back(ocm);
                        pat.clear();
                        pat.push_back(pattern.op(0));
                        pat.push_back(pattern.op(1));
                        N = P = 2;
                        return;
                }
                if (pat.empty())
                        pat.push_back(wilds[0]);
                N = P = 1;
                return;
        }
        for (auto&& w : wilds)
                pat.push_back(w);

        N = ops.size();
        P = pat.size();
        std::optional<CMatcher> ocm;
        size_t len = global_wild? N-1 : P;
        for (size_t i=0; i<len; ++i) {
                perm.push_back(i);
                cms.push_back(ocm);
        }
        all_perms = false;
}

void CMatcher::run()
{
        if (is_exactly_a<power>(source)) {
                noncomm_run();
                return;
        }
        if (all_perms or perm.empty()) {
                ret_val = false;
                return;
        }
        DEBUG std::cerr<<level<<" run() entered"<<std::endl;
        clear_ret();

        if (global_wild)
                with_global_wild();
        else
                no_global_wild();
}

void CMatcher::noncomm_run()
{
        DEBUG std::cerr<<level<<" noncomm_run() entered, N="<<N<<std::endl;
        if (N == 1) {
                if (cms[0]) {
                        auto& cm = cms[0].value();
                        cm.clear_ret();
                        ret_map = cm.get();
                        ret_val = ret_map? true : false;
                        if (ret_val)
                                DEBUG std::cerr<<level<<" send alt: "<<ret_map.value()<<std::endl;
                        return;
                }
                const ex& e = ops[0];
                if (not (is_a<expairseq>(e)
                         or is_a<power>(e)
                         or is_a<function>(e)))
                        throw std::runtime_error("matching gotcha");
/*                         // normal matching attempt
                        exmap m = map;
                        ret_val = e.match(pat[0], m);
                        if (ret_val) {
                                ret_map = m;
        DEBUG std::cerr<<level<<"match found: "<<e<<", "<<pat[0]<<", "<<m<<std::endl;
                        }
                        return;
                }*/
                exmap m = map;
                cms[0].emplace(CMatcher(e, pat[0], m));
                CMatcher& cm = cms[0].value();
                std::optional<exmap> opm = cm.get();
                ret_map = opm;
                ret_val = opm? true : false;
                if (opm)
                        DEBUG std::cerr<<level<<" cmatch found: "<<e<<", "<<pat[0]<<", "<<opm.value()<<std::endl;
                return;
        }
        
        if (N == 2) {
                const ex& e = ops[0];
                if (not (is_a<expairseq>(e)
                         or is_a<power>(e)
                         or is_a<function>(e)))
                        throw std::runtime_error("matching gotcha");
                const ex& ee = ops[1];
                if (not (is_a<expairseq>(ee)
                         or is_a<power>(ee)
                         or is_a<function>(ee)))
                        throw std::runtime_error("matching gotcha");
                if (cms[1]) {
                        auto& cm = cms[1].value();
                        ret_map = cm.get();
                        if (ret_map) {
                                DEBUG std::cerr<<level<<"send alt: "<<ret_map.value()<<std::endl;
                                ret_val = true;
                                return;
                        }
                }
/*                const ex& e = ops[0];
                if (not (is_a<expairseq>(e)
                         or is_a<power>(e)
                         or is_a<function>(e))) {
                         // normal matching attempt
                        exmap m = map;
                        ret_val = e.match(pat[0], m);
                        if (ret_val) {
                                ret_map = m;
        DEBUG std::cerr<<level<<"match found: "<<e<<", "<<pat[0]<<", "<<m<<std::endl;
                        }
                        return;
                }
*/        }

}

void CMatcher::no_global_wild()
{
        std::vector<exmap> map_repo(P);
        // The outer loop goes though permutations of perm
        while (true) {
                size_t index = 0;
                DEBUG { std::cerr<<level<<" ["; for (size_t i:perm) std::cerr<<i<<","; std::cerr<<"]"<<std::endl; }
                // The second loop increases index to get a new ops term
                do {
                        const ex& e = ops[perm[index]];
                        DEBUG std::cerr<<level<<" index: "<<index<<", op: "<<e<<std::endl;
                        if (index == 0)
                                map_repo[0] = map;
                        else
                                map_repo[index] = map_repo[index-1];
                        bool pterm_found = false;
                                // At this point we try matching p to e 
                        const ex& p = pat[index];
                        exmap m = map_repo[index];
                        if (cms[index])
                                cms[index].reset();
                        if (not (is_a<expairseq>(e)
                                 or is_a<power>(e)
                                 or is_a<function>(e))) {
                                // normal matching attempt
                                bool ret = e.match(p, m);
                                if (ret) {
                                        map_repo[index] = m;
                                        pterm_found = true;
                                        DEBUG std::cerr<<level<<" match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                        continue;
                                }
                        }
                        else {
                                cms[index].emplace(CMatcher(e, p, m));
                                CMatcher& cm = cms[index].value();
                                std::optional<exmap> opm = cm.get();
                                if (opm) {
                                        map_repo[index] = opm.value();
                                        pterm_found = true;
                                        DEBUG std::cerr<<level<<" cmatch found: "<<e<<", "<<p<<", "<<map_repo[index]<<std::endl;
                                        continue;
                                }
                                else {
                                        cms[index].reset();
                                }
                        }
                        if (not pterm_found) {
                        // did we start coroutines in this permutation?
                                bool alt_solution_found = false;
                                int i = static_cast<int>(index);
                                while (--i >= 0) {
                                        if (cms[i]) {
                                                CMatcher& cm = cms[i].value();
                                                DEBUG std::cerr<<level<<" find alt: "<<i<<std::endl;
                                                cm.clear_ret();
                                                std::optional<exmap> opm = cm.get();
                                                if (opm) {
                                                        map_repo[i] = opm.value();
                                                        index = i;
                                                        alt_solution_found = true;
                                                        DEBUG std::cerr<<level<<" try alt: "<<i<<", "<<map_repo[i]<<std::endl;
                                                        break;
                                                }
                                                cms[i].reset();
                                        }
                                }
                                if (not alt_solution_found)
                                        break;
                        }
                }
                while (++index < P);

                if (index >= P) {
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
                        DEBUG std::cerr<<level<<" send alt: "<<map_repo[P-1]<<std::endl;
                        ret_val = true;
                        ret_map = map_repo[P-1];
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
                                        DEBUG std::cerr<<level<<" perms exhausted"<<std::endl;
                                        return;
                                }
                        }
                }
        }
        DEBUG std::cerr<<"run() exited"<<std::endl;
        ret_val = false;
}

void CMatcher::with_global_wild()
{
}

}
