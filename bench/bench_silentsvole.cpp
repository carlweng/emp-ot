// SilentSvole generation throughput: time to produce `length` sVOLE
// correlations (F_p and F_2^k carriers), split into the threaded begin()
// prepay (cGGM expand + corrections + check, all wire traffic) and the
// wire-free next_chunks_parallel() produce (cGGM eval + LPN). Both phases
// use the same thread count T. Usage:
//   ./run ./build/bench_silentsvole [log2_len] [threads]
// Correctness lives in test/test_silentsvole.cpp; this is throughput only.
#include "emp-ot/emp-ot.h"
#include "bench/bench.h"
#include <vector>
using namespace emp;
using namespace std;

template <typename SV>
static void bench_gen(NetIO *io, int party, int64_t length, bool malicious,
                      const char *tag, const PrimalLPNParameter &param, int T) {
  using AV = typename SV::AuthValue;
  SV sv(party, io, malicious, param, T);

  const int64_t chunk    = sv.chunk_size();
  const int64_t n_chunks = length / chunk;
  const int64_t eff      = n_chunks * chunk;
  std::vector<AV> buf(eff);

  io->sync();
  auto t0 = clock_start();
  sv.begin(eff);                       // prepay all rounds; begin() threaded by T
  double begin_ms = time_from(t0) / 1000.0;

  io->sync();
  auto t1 = clock_start();
  sv.next_chunks_parallel(buf.data(), n_chunks, T);   // wire-free produce, T threads
  double prod_ms = time_from(t1) / 1000.0;
  sv.end();

  const double total_ms = begin_ms + prod_ms;
  cout << "SilentSvole " << tag << " " << (malicious ? "mali" : "semi")
       << "  T=" << T << "  len=" << eff
       << "  begin=" << begin_ms << "ms  produce=" << prod_ms
       << "ms  total=" << total_ms << "ms  "
       << double(eff) / (total_ms * 1000.0) << " MOTps  (produce "
       << double(eff) / (prod_ms * 1000.0) << " MOTps)" << endl;
}

int main(int argc, char **argv) {
  int length_log = (argc > 2) ? atoi(argv[2]) : 25;     // default 2^25
  const int T    = (argc > 3) ? std::max(1, atoi(argv[3])) : 4;
  if (length_log > 30) { cerr << "Large test size!" << endl; return 1; }
  const int64_t length = 1LL << length_log;

  int party = parse_party(argv);
  int port  = peer_port();
  auto io = (party == ALICE) ? NetIO::listen(port)
                             : NetIO::connect(peer_ip(), port);

  cout << "# bench_silentsvole: length=" << length << " threads=" << T << endl;

  bench_gen<SilentFpVOLE<>>(io.get(), party, length, /*malicious=*/true, "Fp",
                            tuning::ferret_b13, T);
  bench_gen<SilentF2kVOLE<>>(io.get(), party, length, /*malicious=*/true, "F2k",
                             tuning::ferret_b13, T);
  return 0;
}
