#include "ex.h"

#include <vector>
#include <map>
#include <optional>



namespace GiNaC {

struct CMatcher;

struct CMatcher {
        CMatcher(const ex &source_, const ex & pattern_, exmap& map_)
         : source(source_), pattern(pattern_), map(map_) { init(); }
        void init();
        void run();
        std::optional<exmap> get()
        {
                if (ret_val) {
                        // it was already done in init()
                        return ret_map;
                }
                run();    // guarantees to set ret, and if true, map
                return ret_map;
        }
        void clear_ret()
        {
                ret_val.reset();
                ret_map.reset();
        }

        ex source, pattern;
        std::optional<bool> ret_val;
        std::optional<exmap> ret_map;

        // the state consists of the following
        exmap map;
        size_t N{0};
        exvector ops, pat;
        std::vector<size_t> perm;
        std::vector<std::optional<CMatcher>> cms;
        bool all_perms;
};

}
