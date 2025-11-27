// Fuzz target for SPI checksum calculation
// This is a standalone target that doesn't require full openpilot build
//
// Build:
//   clang++ -g -O1 -fsanitize=fuzzer,address \
//       fuzz/libfuzzer/fuzz_spi_checksum.cc \
//       -o fuzz/libfuzzer/fuzz_spi_checksum
//
// Run:
//   ./fuzz/libfuzzer/fuzz_spi_checksum fuzz/corpus/spi_checksum/

#include <cstdint>
#include <cstddef>
#include <cstring>

// SPI protocol constants from spi.cc
#define SPI_SYNC 0x5AU
#define SPI_HACK 0x79U
#define SPI_DACK 0x85U
#define SPI_NACK 0x1FU
#define SPI_CHECKSUM_START 0xABU

// Simplified checksum calculation based on openpilot SPI protocol
uint8_t calculate_checksum(const uint8_t *data, size_t len) {
    uint8_t checksum = SPI_CHECKSUM_START;
    for (size_t i = 0; i < len; i++) {
        checksum ^= data[i];
    }
    return checksum;
}

// Parse SPI packet header
struct __attribute__((packed)) SPIHeader {
    uint8_t sync;
    uint8_t endpoint;
    uint16_t tx_len;
    uint16_t max_rx_len;
};

bool validate_spi_packet(const uint8_t *data, size_t size) {
    if (size < sizeof(SPIHeader) + 1) {
        return false;  // Too small
    }

    const SPIHeader *header = reinterpret_cast<const SPIHeader*>(data);

    // Check sync byte
    if (header->sync != SPI_SYNC) {
        return false;
    }

    // Validate lengths
    if (header->tx_len > 4096 || header->max_rx_len > 4096) {
        return false;
    }

    // Check if we have enough data for the payload + checksum
    size_t expected_size = sizeof(SPIHeader) + header->tx_len + 1;
    if (size < expected_size) {
        return false;
    }

    // Validate checksum
    uint8_t expected_checksum = calculate_checksum(data, sizeof(SPIHeader) + header->tx_len);
    uint8_t actual_checksum = data[sizeof(SPIHeader) + header->tx_len];

    return expected_checksum == actual_checksum;
}

// Process a response packet
bool process_response(const uint8_t *data, size_t size) {
    if (size < 3) return false;

    uint8_t response_type = data[0];
    uint16_t data_len = data[1] | (data[2] << 8);

    if (response_type == SPI_HACK || response_type == SPI_DACK) {
        if (size < 3 + data_len + 1) return false;

        // Validate response checksum
        uint8_t expected = calculate_checksum(data, 3 + data_len);
        uint8_t actual = data[3 + data_len];

        return expected == actual;
    }

    return response_type == SPI_NACK;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size == 0) return 0;

    // Test packet validation
    validate_spi_packet(data, size);

    // Test response processing
    process_response(data, size);

    // Test checksum calculation with various sizes
    if (size > 0) {
        calculate_checksum(data, size);
    }
    if (size > 10) {
        calculate_checksum(data + 5, size - 5);
    }

    return 0;
}
