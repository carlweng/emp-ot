// SilentSvole correctness: all wire traffic at begin(), wire-free
// next()/produce_range()/end(). Verifies sVOLE triple correctness for both
// carriers (F2k + F_p), semi-honest and malicious, with a begin()-time pool;
// asserts the consume path moves zero bytes ("silent"); and checks that
// produce_range() over disjoint ranges is byte-identical to the serial path.
#include "emp-ot/emp-ot.h"
#include "emp-tool/emp-tool.h"
#include <thread>
#include <vector>

using namespace emp;
using namespace std;

int party, port;

// --- Oracle checks: BOB ships Δ and the mac side; the Δ-holder re-derives. ---

// F2k: holder is BOB. mac == gfmul(Δ, val) ^ key (key is the non-holder's mac).
static void check_f2k(NetIO *io, int holder, const AuthValueF2k *v,
                      int64_t n, block Delta) {
  if (party == holder) {
    io->send_data(&Delta, sizeof(block));
    std::vector<block> mac(n);
    for (int64_t i = 0; i < n; ++i) mac[i] = v[i].mac;
    io->send_data(mac.data(), n * sizeof(block));
    io->flush();
  } else {
    block d_;
    std::vector<block> k(n);   // holder's mac (the key K_i)
    io->recv_data(&d_, sizeof(block));
    io->recv_data(k.data(), n * sizeof(block));
    for (int64_t i = 0; i < n; ++i) {
      block tmp;               // expect mac == gfmul(Δ, val) ^ K
      gfmul(d_, v[i].val, &tmp);
      tmp = tmp ^ k[i];
      if (memcmp(&tmp, &v[i].mac, sizeof(block)) != 0)
        error("F2k triple error");
    }
  }
}

// Fp: holder is ALICE. mac == (val*Δ + key) mod p.
static void check_fp(NetIO *io, int holder, const AuthValueFp *v, int64_t n,
                     uint64_t Delta) {
  using AV = AuthValueFp;
  if (party == holder) {
    io->send_data(&Delta, sizeof(uint64_t));
    std::vector<uint64_t> mac(n);
    for (int64_t i = 0; i < n; ++i) mac[i] = v[i].mac;
    io->send_data(mac.data(), n * sizeof(uint64_t));
    io->flush();
  } else {
    uint64_t d_;
    std::vector<uint64_t> k(n);
    io->recv_data(&d_, sizeof(uint64_t));
    io->recv_data(k.data(), n * sizeof(uint64_t));
    for (int64_t i = 0; i < n; ++i) {
      uint64_t want = AV::f_add(AV::f_mul(v[i].val, d_), k[i]);
      if (want != v[i].mac) error("Fp triple error");
    }
  }
}

static constexpr auto kParam   = tuning::ferret_b11;
static constexpr int  kThreads = 4;

template <typename SV, typename Check>
static void run_carrier(NetIO *io, int holder, bool malicious, Check check) {
  using AV = typename SV::AuthValue;

  // (1) Silent property + streaming correctness over a couple of rounds.
  {
    SV sv(party, io, malicious, kParam, kThreads);
    const bool is_holder = (party == holder);
    // F2k auto-samples Δ; Fp needs an explicit Δ injected by the holder.
    typename AV::F Delta = AV::f_zero();
    if (is_holder) Delta = sv.delta();

    const int64_t chunk = sv.chunk_size();
    const int64_t rc    = sv.round_capacity();
    const int64_t n_chunks = std::min<int64_t>(rc, 64);
    std::vector<AV> buf(n_chunks * chunk);

    io->sync();
    sv.begin();
    const uint64_t s0 = io->send_counter, r0 = io->recv_counter;
    for (int64_t i = 0; i < n_chunks; ++i) sv.next(buf.data() + i * chunk);
    if (io->send_counter != s0 || io->recv_counter != r0)
      error("SilentSvole next() performed wire I/O (not silent)");
    sv.end();
    if (io->send_counter != s0 || io->recv_counter != r0)
      error("SilentSvole end() performed wire I/O (not silent)");

    check(io, holder, buf.data(), n_chunks * chunk, Delta);
    cout << "  silent next/end ok (" << n_chunks << " chunks, "
         << (malicious ? "mali" : "semi") << ")" << endl;
  }

  // (2) produce_range() over disjoint ranges == serial, and verifies.
  {
    SV sv(party, io, malicious, kParam, kThreads);
    const bool is_holder = (party == holder);
    typename AV::F Delta = AV::f_zero();
    if (is_holder) Delta = sv.delta();

    const int64_t chunk = sv.chunk_size();
    io->sync();
    sv.begin();
    const int64_t n = std::min<int64_t>(sv.round_capacity(), 64);
    std::vector<AV> a(n * chunk), b(n * chunk);

    sv.produce_range(a.data(), 0, n);                 // single call
    // n threads on disjoint ranges.
    std::vector<std::thread> ths;
    const int64_t per = (n + kThreads - 1) / kThreads;
    for (int t = 0; t < kThreads; ++t) {
      const int64_t beg = t * per;
      if (beg >= n) break;
      const int64_t cnt = std::min<int64_t>(per, n - beg);
      ths.emplace_back([&, beg, cnt]() {
        sv.produce_range(b.data() + beg * chunk, beg, cnt);
      });
    }
    for (auto &th : ths) th.join();
    if (memcmp(a.data(), b.data(), n * chunk * sizeof(AV)) != 0)
      error("SilentSvole produce_range not order/thread-independent");
    sv.end();
    check(io, holder, a.data(), n * chunk, Delta);
    cout << "  produce_range ok (" << n << " chunks, "
         << (malicious ? "mali" : "semi") << ")" << endl;
  }

  // (3) Multi-round prepay: begin(n_ots) prepares K rounds; the whole prepared
  // capacity is drawn across rounds with NO wire I/O, behind one batched check.
  {
    SV sv(party, io, malicious, kParam, kThreads);
    const bool is_holder = (party == holder);
    typename AV::F Delta = AV::f_zero();
    if (is_holder) Delta = sv.delta();

    const int64_t chunk = sv.chunk_size();
    io->sync();
    sv.begin(3 * sv.cots_per_round());                 // K = 3 rounds prepaid
    const uint64_t s0 = io->send_counter, r0 = io->recv_counter;
    const int64_t cap = sv.prepared_capacity();
    std::vector<AV> buf(cap);
    sv.next_chunks_parallel(buf.data(), cap / chunk);  // wire-free across rounds
    if (io->send_counter != s0 || io->recv_counter != r0)
      error("SilentSvole prepaid consume performed wire I/O (not silent)");
    sv.end();
    check(io, holder, buf.data(), cap, Delta);
    cout << "  prepaid " << (cap / chunk) << " chunks ok (" << (cap / chunk /
            sv.round_capacity()) << " rounds, "
         << (malicious ? "mali" : "semi") << ")" << endl;
  }
}

int main(int argc, char **argv) {
  party = parse_party(argv);
  port = peer_port();
  auto io = (party == ALICE) ? NetIO::listen(port)
                             : NetIO::connect(peer_ip(), port);

  for (bool mali : {false, true}) {
    cout << "--- SilentF2kVOLE " << (mali ? "mali" : "semi") << " ---" << endl;
    run_carrier<SilentF2kVOLE<>>(io.get(), /*holder=*/BOB, mali, check_f2k);
    cout << "--- SilentFpVOLE " << (mali ? "mali" : "semi") << " ---" << endl;
    run_carrier<SilentFpVOLE<>>(io.get(), /*holder=*/ALICE, mali, check_fp);
  }
  cout << "Tests passed." << endl;
  return 0;
}
