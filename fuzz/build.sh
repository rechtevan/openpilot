#!/bin/bash
# Build script for openpilot fuzz targets
set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$ROOT_DIR"

echo "=== Building Fuzz Targets ==="
echo ""

# Check for clang
if command -v clang++ &> /dev/null; then
    CLANG_CXX="clang++"
else
    echo "WARNING: clang++ not found, libFuzzer targets will not be built"
    CLANG_CXX=""
fi

# Check for AFL++
if command -v afl-c++ &> /dev/null; then
    AFL_CXX="afl-c++"
else
    echo "WARNING: afl-c++ not found, AFL++ targets will not be built"
    AFL_CXX=""
fi

# Create output directories
mkdir -p fuzz/libfuzzer fuzz/aflpp fuzz/corpus fuzz/findings

# Build libFuzzer targets
if [ -n "$CLANG_CXX" ]; then
    echo "Building libFuzzer targets..."

    # SPI checksum fuzzer (standalone)
    echo "  - fuzz_spi_checksum"
    $CLANG_CXX -g -O1 -fno-omit-frame-pointer \
        -fsanitize=fuzzer,address,undefined \
        fuzz/libfuzzer/fuzz_spi_checksum.cc \
        -o fuzz/libfuzzer/fuzz_spi_checksum

    echo "libFuzzer targets built successfully"
else
    echo "Skipping libFuzzer targets (clang++ not available)"
fi

echo ""

# Build AFL++ targets
if [ -n "$AFL_CXX" ]; then
    echo "Building AFL++ targets..."

    # SPI checksum fuzzer (standalone)
    echo "  - fuzz_spi_checksum_afl"
    $AFL_CXX -g -O2 \
        fuzz/aflpp/fuzz_spi_checksum_afl.cc \
        -o fuzz/aflpp/fuzz_spi_checksum_afl

    echo "AFL++ targets built successfully"
else
    echo "Skipping AFL++ targets (afl-c++ not available)"
fi

echo ""
echo "=== Build Complete ==="
echo ""
echo "To run libFuzzer:"
echo "  ./fuzz/libfuzzer/fuzz_spi_checksum fuzz/corpus/spi_checksum/"
echo ""
echo "To run AFL++:"
echo "  afl-fuzz -i fuzz/seeds/spi_checksum -o fuzz/findings/spi_checksum ./fuzz/aflpp/fuzz_spi_checksum_afl @@"
