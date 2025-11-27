// AFL++ fuzz target for SPI checksum/packet validation
// Standalone - no openpilot library dependencies
//
// Build:
//   afl-c++ -g -O2 -fsanitize=address \
//       fuzz/aflpp/fuzz_spi_checksum_afl.cc \
//       -o fuzz/aflpp/fuzz_spi_checksum_afl
//
// Run:
//   mkdir -p fuzz/seeds/spi_checksum fuzz/findings/spi_checksum
//   echo -ne '\x5a\x01\x00\x00\x00\x00\xab' > fuzz/seeds/spi_checksum/seed1
//   afl-fuzz -i fuzz/seeds/spi_checksum -o fuzz/findings/spi_checksum \
//       ./fuzz/aflpp/fuzz_spi_checksum_afl @@

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>

// SPI protocol constants
#define SPI_SYNC 0x5AU
#define SPI_HACK 0x79U
#define SPI_DACK 0x85U
#define SPI_NACK 0x1FU
#define SPI_CHECKSUM_START 0xABU

uint8_t calculate_checksum(const uint8_t *data, size_t len) {
    uint8_t checksum = SPI_CHECKSUM_START;
    for (size_t i = 0; i < len; i++) {
        checksum ^= data[i];
    }
    return checksum;
}

struct __attribute__((packed)) SPIHeader {
    uint8_t sync;
    uint8_t endpoint;
    uint16_t tx_len;
    uint16_t max_rx_len;
};

bool validate_spi_packet(const uint8_t *data, size_t size) {
    if (size < sizeof(SPIHeader) + 1) {
        return false;
    }

    const SPIHeader *header = reinterpret_cast<const SPIHeader*>(data);

    if (header->sync != SPI_SYNC) {
        return false;
    }

    if (header->tx_len > 4096 || header->max_rx_len > 4096) {
        return false;
    }

    size_t expected_size = sizeof(SPIHeader) + header->tx_len + 1;
    if (size < expected_size) {
        return false;
    }

    uint8_t expected_checksum = calculate_checksum(data, sizeof(SPIHeader) + header->tx_len);
    uint8_t actual_checksum = data[sizeof(SPIHeader) + header->tx_len];

    return expected_checksum == actual_checksum;
}

bool process_response(const uint8_t *data, size_t size) {
    if (size < 3) return false;

    uint8_t response_type = data[0];
    uint16_t data_len = data[1] | (data[2] << 8);

    if (response_type == SPI_HACK || response_type == SPI_DACK) {
        if (size < 3 + data_len + 1) return false;

        uint8_t expected = calculate_checksum(data, 3 + data_len);
        uint8_t actual = data[3 + data_len];

        return expected == actual;
    }

    return response_type == SPI_NACK;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input_file>\n", argv[0]);
        return 1;
    }

    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror("fopen");
        return 1;
    }

    fseek(f, 0, SEEK_END);
    size_t size = ftell(f);
    fseek(f, 0, SEEK_SET);

    if (size == 0) {
        fclose(f);
        return 0;
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

    // Exercise the parsing code
    validate_spi_packet(data, size);
    process_response(data, size);

    if (size > 0) {
        calculate_checksum(data, size);
    }
    if (size > 10) {
        calculate_checksum(data + 5, size - 5);
    }

    free(data);
    return 0;
}
