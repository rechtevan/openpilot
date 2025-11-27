// AFL++ fuzz target for CAN Cap'n Proto message parsing
// Build: afl-c++ -g -O2 -fsanitize=address -I. -Icereal -Imsgq \
//        fuzz/aflpp/fuzz_can_capnp_afl.cc -o fuzz/aflpp/fuzz_can_capnp_afl \
//        -Lbuild -lcereal -lmsgq

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <string>
#include <vector>

#include "selfdrive/pandad/can_types.h"

// Forward declaration
void can_capnp_to_can_list_cpp(const std::vector<std::string> &strings,
                                std::vector<CanData> &can_list, bool sendcan);

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
        return 1;
    }

    // Read input file
    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror("fopen");
        return 1;
    }

    fseek(f, 0, SEEK_END);
    size_t size = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (size < 8) {
        fclose(f);
        return 0;  // Too small for Cap'n Proto
    }

    uint8_t *data = (uint8_t*)malloc(size);
    if (!data) {
        fclose(f);
        return 1;
    }

    if (fread(data, 1, size, f) != size) {
        free(data);
        fclose(f);
        return 1;
    }
    fclose(f);

    // Parse the data
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

    free(data);
    return 0;
}
