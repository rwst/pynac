#include "ex.h"
#include "optional.hpp"

#include <vector>
#include <map>



namespace GiNaC {

struct CMatcher;
using opt_exmap = nonstd::optional<exmap>;
using opt_bool = nonstd::optional<bool>;
using opt_CMatcher = nonstd::optional<CMatcher>;
using nonstd::nullopt;

struct CMatcher_state {
};

struct CMatcher {
        CMatcher(const ex &source_, const ex & pattern_, exmap& map_)
         : source(source_), pattern(pattern_), map(map_)
            { ret_val = init(); finished = bool(ret_val); }
        //~CMatcher() { --level; } 
        opt_bool init();
        void run();
        void noncomm_run();
        void no_global_wild();
        void with_global_wild();
        opt_exmap get()
        {
                if (ret_val) {
                        if (not ret_val.value())
                                return nullopt;
                        ret_val.reset();
                }
                ret_map.reset();
                ++level;
                run();    // guarantees to set ret, and if true, map
                --level;
                return ret_map;
        }
        CMatcher& make_cmatcher(const ex& e, size_t i, exmap& mm);
        bool get_alt(size_t);
        void clear_ret()
        {
                ret_val.reset();
                ret_map.reset();
        }

        static int level;
        ex source, pattern;
        opt_bool ret_val;
        opt_exmap ret_map;

        // the state consists of the following
        exmap map;
        size_t N{0}, P{0}, last_alt;
        exvector ops, pat;
        std::vector<opt_CMatcher> cms;
        std::vector<exmap> map_repo;
        std::vector<bool> m_cmatch, m_finished;
        bool finished{false}, global_wild{false};
        std::vector<size_t> perm;
        enum Type { unset, comm, noncomm, comm_plus };
        Type type {unset};
};

}
