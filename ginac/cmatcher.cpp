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

inline bool is_func(const ex& e)
{
        return is_exactly_a<power>(e)
            or is_exactly_a<function>(e)
            or is_a<expairseq>(e);
}

inline bool is_ncfunc(const ex& e)
{
        return is_exactly_a<power>(e)
            or is_exactly_a<function>(e);
}

inline CMatcher& CMatcher::make_cmatcher(const ex& e, size_t i, exmap& mm)
{
        exmap m = mm;
        cms[i].emplace(CMatcher(e, pat[i], m));
        return cms[i].value();
}

inline bool CMatcher::get_alt(CMatcher& cm)
{
        if (cm.ret_val and not cm.ret_val.value())
                return false;
        bool ret;
        const opt_exmap& opm = cm.get();
        ret_map = opm;
        ret_val = ret = opm? true : false;
        if (ret)
                DEBUG std::cerr<<level<<" cmatch found: "<<opm.value()<<std::endl;
        return ret;
}

opt_bool CMatcher::init()
{
        DEBUG std::cerr<<level<<" cmatch: "<<source<<", "<<pattern<<", "<<map<<std::endl;
        const size_t snops = source.nops(), pnops = pattern.nops();
	if (is_exactly_a<wildcard>(pattern)) {
                DEBUG std::cerr << "pattern is single wildcard"<<std::endl;
                const auto& it = map.find(pattern);
                if (it != map.end()) {
		        if (not source.is_equal(ex_to<basic>(it->second)))
                                return false;
                        ret_map = map;
                        return true;
                }
		map[pattern] = source;
                ret_map = map;
		return true;
	} 
	if (ex_to<basic>(source).tinfo() != ex_to<basic>(pattern).tinfo()) {
                DEBUG std::cerr<<"pattern type mismatch"<<std::endl;
                return false;
        }
        if (is_exactly_a<function>(source)
           and ex_to<function>(source).get_serial()
            != ex_to<function>(pattern).get_serial()) {
                DEBUG std::cerr<<"function type mismatch"<<std::endl;
                return false;
        }
        if (snops < pnops) {
                DEBUG std::cerr<<"# of source terms > pattern terms"<<std::endl;
                return false;
        }
        symbolset oset = source.symbols();
        symbolset pset = substitute(pattern.wilds(), map);
        if (not subset_of(pset, oset)) {
                DEBUG std::cerr<<"substitution has unmatched symbols"<<std::endl;
                return false;
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
                        return false;
                }
        }
        if (not is_ncfunc(source) and snops > pnops) {
                if (wilds.empty())
                        return false;
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
                        return false;
                }
                        DEBUG std::cerr<<level<<" constant "<<*it1<<" found in "<<source<<std::endl;
                it1 = pat.erase(it1);
        }
        if (wilds.empty() and ops.empty() and pat.empty()) {
                ret_map = map;
                return true;
        }
        if (wilds.empty() and (ops.empty() or pat.empty()))
                throw std::runtime_error("matching gotcha");

        for (auto&& w : wilds)
                pat.push_back(w);
        
        N = ops.size();
        P = pat.size();
        size_t len = global_wild? N-1 : P;
        for (size_t i=0; i<len; ++i) {
                cms.emplace_back();
        }
        
        if (is_ncfunc(source)) {
                if (pat.empty())
                        throw std::runtime_error("matching gotcha");
                size_t i;
                for (i=0; i<N; ++i) {
                        if (is_func(ops[i]))
                                break;
                        if (not ops[i].match(pat[i], map))
                                return false;
                }
                if (i == N) {
                        ret_map = map;
                        return true;
                }
                return {};
        }

        for (size_t i=0; i<len; ++i) {
                perm.push_back(i);
        }
        all_perms = false;
        return {};
}

void CMatcher::run()
{
        clear_ret();
        if (is_ncfunc(source)) {
                noncomm_run();
                return;
        }
        if (all_perms or perm.empty()) {
                ret_val = false;
                return;
        }

        if (global_wild)
                with_global_wild();
        else
                no_global_wild();
}

void CMatcher::noncomm_run()
{
        std::vector<exmap> map_repo(P);
        DEBUG std::cerr<<level<<" noncomm_run() entered, N="<<N<<std::endl;
        // TODO: generalize, refactor
        if (N == 1) {
                if (not is_func(ops[0])) {
                        ret_val = false;
                        return;
                }
                if (cms[0]) {
                        get_alt(cms[0].value());
                        return;
                }
                get_alt(make_cmatcher(ops[0], 0, map));
                return;
        }
        
        if (N == 2) {
                const ex& e = ops[0];
                const ex& ee = ops[1];
                if (not (is_func(e) and is_func(ee))) {
                        ret_val = false;
                        return;
                }
                if (not (is_func(e))) {
                        if (cms[1]) {
                                get_alt(cms[1].value());
                                return;
                        }
                        if (not e.match(pat[0], map)) {
                                ret_val = false;
                                return;
                        }
                        get_alt(make_cmatcher(ee, 1, map));
                        return;
                }
                if (not (is_func(ee))) {
                        bool ret;
                        if (cms[0])
                                ret = get_alt(cms[0].value());
                        else
                                ret = get_alt(make_cmatcher(e, 0, map));
                        if (not ret) {
                                ret_val = false;
                                return;
                        }
                        ret_val = e.match(pat[1], ret_map.value());
                        return;
                }
        }
        // both ops are funcs
        size_t index = 0;
        // The second loop increases index to get a new ops term
        do {
                const ex& e = ops[index];
                DEBUG std::cerr<<level<<" index: "<<index<<", op: "<<e<<std::endl;
                if (index == 0)
                        map_repo[0] = map;
                else
                        map_repo[index] = map_repo[index-1];
                // At this point we try matching p to e 
                const ex& p = pat[index];
                if (cms[index])
                        cms[index].reset();
                if (not is_func(e)) {
                        // normal matching attempt
                        exmap m = map_repo[index];
                        bool ret = e.match(p, m);
                        if (ret) {
                                map_repo[index] = m;
                                DEBUG std::cerr<<level<<" match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                continue;
                        }
                }
                else {
                        if (get_alt(make_cmatcher(e, index,
                                                  map_repo[index]))) {
                                map_repo[index] = ret_map.value();
                                continue;
                        }
                        else
                                cms[index].reset();
                }
                bool alt_solution_found = false;
                int i = static_cast<int>(index);
                while (--i >= 0) {
                        if (cms[i]) {
                                DEBUG std::cerr<<level<<" find alt: "<<i<<std::endl;
                                if (get_alt(cms[i].value())) {
                                        map_repo[i] = ret_map.value();
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
        while (++index < P);

        if (index >= P) {
                DEBUG std::cerr<<level<<" send alt: "<<map_repo[P-1]<<std::endl;
                ret_val = true;
                ret_map = map_repo[P-1];
                return;
        }
        ret_val = false;
}

void CMatcher::no_global_wild()
{
        DEBUG std::cerr<<level<<" run() entered"<<std::endl;
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
                        // At this point we try matching p to e 
                        const ex& p = pat[index];
                        if (cms[index])
                                cms[index].reset();
                        if (not is_func(e)) {
                                // normal matching attempt
                                exmap m = map_repo[index];
                                bool ret = e.match(p, m);
                                if (ret) {
                                        map_repo[index] = m;
                                        DEBUG std::cerr<<level<<" match found: "<<e<<", "<<p<<", "<<m<<": "<<ret<<std::endl; 
                                        continue;
                                }
                        }
                        else {
                                if (get_alt(make_cmatcher(e, index,
                                                          map_repo[index]))) {
                                        map_repo[index] = ret_map.value();
                                        continue;
                                }
                                else
                                        cms[index].reset();
                        }
                        // did we start coroutines in this permutation?
                        bool alt_solution_found = false;
                        int i = static_cast<int>(index);
                        while (--i >= 0) {
                                if (cms[i]) {
                                        DEBUG std::cerr<<level<<" find alt: "<<i<<std::endl;
                                        if (get_alt(cms[i].value())) {
                                                map_repo[i] = ret_map.value();
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
        DEBUG std::cerr<<"noncomm_run() exited"<<std::endl;
        ret_val = false;
}

void CMatcher::with_global_wild()
{
        DEBUG std::cerr<<level<<" gwrun() entered"<<std::endl;
}

}
