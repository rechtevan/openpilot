# Fuzzing Setup for openpilot

This directory contains fuzzing infrastructure for openpilot using libFuzzer and AFL++.

## Quick Start

```bash
# Build all fuzz targets
./fuzz/build.sh

# Run libFuzzer (fast, in-process fuzzing)
./fuzz/libfuzzer/fuzz_spi_checksum fuzz/corpus/spi_checksum/

# Run AFL++ (requires environment variables on some systems)
AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 \
    afl-fuzz -i fuzz/seeds/spi_checksum -o fuzz/findings/spi_checksum \
    ./fuzz/aflpp/fuzz_spi_checksum_afl @@
```

## Prerequisites

### Install Dependencies

```bash
# Ubuntu/Debian
sudo apt-get update
sudo apt-get install -y clang llvm afl++ libasan6

# Verify installations
clang++ --version
afl-fuzz --version
```

## Directory Structure

```
fuzz/
├── libfuzzer/     # libFuzzer targets (built binaries)
├── aflpp/         # AFL++ targets (built binaries)
├── corpus/        # Corpus for libFuzzer (grows during fuzzing)
├── seeds/         # Initial seed inputs for AFL++
├── findings/      # AFL++ crash/hang outputs
├── build.sh       # Build script for all targets
└── README.md      # This file
```

## Available Fuzz Targets

### SPI Checksum Parser (`fuzz_spi_checksum`)
Tests the SPI protocol packet validation and checksum calculation used for
communication with the panda device. This is safety-critical code.

**libFuzzer:**
```bash
./fuzz/libfuzzer/fuzz_spi_checksum fuzz/corpus/spi_checksum/
```

**AFL++:**
```bash
AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 \
    afl-fuzz -i fuzz/seeds/spi_checksum -o fuzz/findings/spi_checksum \
    ./fuzz/aflpp/fuzz_spi_checksum_afl @@
```

## libFuzzer Usage

libFuzzer is built into Clang and provides coverage-guided fuzzing.

### libFuzzer Options

```bash
# Run with specific options
./fuzz_target corpus/ \
    -max_len=4096 \           # Max input size
    -timeout=10 \             # Timeout per run (seconds)
    -jobs=4 \                 # Parallel jobs
    -workers=4 \              # Worker processes
    -dict=fuzz/dicts/can.dict # Dictionary file
```

## AFL++ Usage

AFL++ is a powerful fuzzer with many mutation strategies.

### Build with AFL++ instrumentation

```bash
cd /path/to/openpilot

# Build with afl-clang-fast++
afl-clang-fast++ -g -O2 \
    -fsanitize=address \
    -I. -Icereal -Imsgq -Icommon \
    fuzz/aflpp/fuzz_can_parser_afl.cc \
    -o fuzz/aflpp/fuzz_can_parser_afl

# Create seed directory with sample inputs
mkdir -p fuzz/seeds/can_parser
echo -e '\x00\x00\x00\x08\x01\x02\x03\x04' > fuzz/seeds/can_parser/seed1

# Run AFL++
afl-fuzz -i fuzz/seeds/can_parser -o fuzz/findings/can_parser \
    ./fuzz/aflpp/fuzz_can_parser_afl @@
```

### AFL++ Options

```bash
afl-fuzz \
    -i seeds/ \               # Input seeds directory
    -o findings/ \            # Output directory
    -m none \                 # No memory limit
    -t 1000 \                 # Timeout (ms)
    -x dict.txt \             # Dictionary
    -- ./target @@            # @@ = input file placeholder
```

## Fuzz Targets

### Priority Targets

1. **CAN Message Parsing** - Safety-critical, parses untrusted vehicle data
2. **Cereal Deserialization** - Parses Cap'n Proto messages
3. **SPI Protocol** - Hardware communication protocol
4. **Camera Frame Parsing** - Complex binary data

### Writing a Fuzz Target

```cpp
// libFuzzer target template
#include <cstdint>
#include <cstddef>

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    // Call the function you want to fuzz
    // parse_can_message(data, size);
    return 0;
}
```

```cpp
// AFL++ target template
#include <cstdio>
#include <cstdlib>

int main(int argc, char **argv) {
    if (argc < 2) return 1;

    FILE *f = fopen(argv[1], "rb");
    if (!f) return 1;

    fseek(f, 0, SEEK_END);
    size_t size = ftell(f);
    fseek(f, 0, SEEK_SET);

    uint8_t *data = (uint8_t*)malloc(size);
    fread(data, 1, size, f);
    fclose(f);

    // Call the function you want to fuzz
    // parse_can_message(data, size);

    free(data);
    return 0;
}
```

## Corpus Management

```bash
# Minimize corpus
afl-cmin -i corpus/ -o corpus_min/ -- ./target @@

# Merge corpora
./fuzz_target -merge=1 corpus/ new_corpus/
```

## Analyzing Crashes

```bash
# Reproduce a crash
./fuzz_target crash-file

# Get stack trace with ASan
ASAN_OPTIONS=symbolize=1 ./fuzz_target crash-file

# Minimize crash input
afl-tmin -i crash-file -o crash-min -- ./target @@
```
