// Fuzz target for CAN Cap'n Proto message parsing
// Build: clang++ -g -O1 -fsanitize=fuzzer,address -I. -Icereal -Imsgq \
//        fuzz/libfuzzer/fuzz_can_capnp.cc -o fuzz/libfuzzer/fuzz_can_capnp \
//        -Lbuild -lcereal -lmsgq

#include <cstdint>
#include <cstddef>
#include <string>
#include <vector>

#include "selfdrive/pandad/can_types.h"

// Forward declaration - we'll link against the actual implementation
void can_capnp_to_can_list_cpp(const std::vector<std::string> &strings,
                                std::vector<CanData> &can_list, bool sendcan);

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 8) return 0;  // Cap'n Proto needs minimum size

    // Create input string from fuzz data
    std::string input(reinterpret_cast<const char*>(data), size);
    std::vector<std::string> strings = {input};
    std::vector<CanData> can_list;

    // Try parsing as regular CAN
    try {
        can_capnp_to_can_list_cpp(strings, can_list, false);
    } catch (...) {
        // Expected for malformed input
    }

    // Try parsing as sendcan
    can_list.clear();
    try {
        can_capnp_to_can_list_cpp(strings, can_list, true);
    } catch (...) {
        // Expected for malformed input
    }

    return 0;
}
