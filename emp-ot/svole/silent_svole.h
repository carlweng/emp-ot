#ifndef EMP_OT_SVOLE_SILENT_SVOLE_H__
#define EMP_OT_SVOLE_SILENT_SVOLE_H__

#include "emp-ot/svole/f2k_vole.h"
#include "emp-ot/svole/fp_vole.h"
#include "emp-ot/svole/svole.h"
#include <emp-tool/emp-tool.h>   // ThreadPool
#include <algorithm>
#include <memory>
#include <vector>

namespace emp {

/*
 * SilentSvole<AuthValue> — an sVOLE extension whose consume path does NO
 * wire I/O, the carrier-generic twin of SilentFerret (F2k and F_p).
 *
 * begin() / begin(n_ots) concentrate the whole prepay up front:
 *   1. the inner Ferret RCOT pull (base COTs for each round's MPFSS),
 *   2. every tree's cGGM correction + secret_sum, shipped in tree order via
 *      the gadget's batched prepare_all() (which folds the chi-fold
 *      accumulators), and
 *   3. ONE FTyped consistency check over the whole batch (m = K*t trees).
 * next() / produce_range() then re-derive each tree LOCALLY — cGGM
 * produce_tree + α-slot val insertion + LPN amplification — with the wire idle.
 *
 * Prepaid multi-round (begin(n_ots)): K = ceil(n_ots / cots_per_round()) rounds
 * are prepared back-to-back. All RCOT pulls and all corrections ship during
 * begin(); each round's base COTs (receiver), corrections, secret_sums, and
 * carry triples are retained so any tree of any prepaid round re-derives with
 * no I/O. The single batched FTyped check (the linear per-round checks summed)
 * closes the batch. Resident state is O(K). No-arg begin() is the K = 1 case,
 * byte-identical to live Svole (the batched check degenerates to run_end_typed),
 * with a live end()+begin() rollover when the round's budget is exhausted.
 *
 * Threading: prepare_all() parallelizes the begin()-time cGGM expand / VW fold
 * over an internal ThreadPool (n_threads); the wire-free consume can be fanned
 * out via produce_range() / next_chunks_parallel(). Each tree is re-derived
 * deterministically from its global counter G = abs_round*t + local_tree, so
 * output is order- and thread-independent and identical to the serial path.
 */
template <typename AuthValue_>
class SilentSvole : public Svole<AuthValue_> {
  using Base = Svole<AuthValue_>;
  static constexpr int kMaxTreeDepth = 32;

 public:
  using AuthValue = AuthValue_;
  using F         = typename AuthValue::F;

  // `n_threads` sizes the begin()-time expansion pool (<=1 → serial, no pool)
  // and the default fan-out of next_chunks_parallel(). Other args mirror Svole.
  SilentSvole(int party, IOChannel *io, bool malicious = true,
              PrimalLPNParameter param = tuning::ferret_b13, int n_threads = 1)
      : Base(party, io, malicious, param),
        n_threads_(n_threads < 1 ? 1 : n_threads) {
    leave_n_ = int64_t{1} << this->param.tree_depth;
    M_       = svole_M(this->param);
    bpc_     = this->lpn_->blocks_per_chunk(this->chunk_size());
    batch_   = (n_threads_ <= 1) ? 1 : n_threads_ * 8;
    lpn_key_       = zero_block;
    cggm_seed_key_ = zero_block;
  }
  ~SilentSvole() override = default;

  // Consume path moves no bytes for either role — all traffic is in begin().
  static constexpr bool kSenderSendsOnExtend = false;

  // User-visible trees (chunks) per round and across the whole prepaid batch.
  int64_t round_capacity() const {
    return this->param.t - this->param.refill_trees;
  }
  int64_t cots_per_round() const { return round_capacity() * this->chunk_size(); }
  int64_t prepared_capacity() const { return n_rounds_ * cots_per_round(); }

  // Single-round begin (== begin(cots_per_round()), K = 1).
  void begin() override { begin_batch_(cots_per_round()); }

  // Prepaid begin: prepare enough rounds that up to `n_ots` outputs can be drawn
  // with NO wire I/O. All correction traffic and the single batched check happen
  // here. After this, draw up to prepared_capacity() outputs via next() /
  // next_n() / run() (auto-rolls rounds wire-free), next_chunks_parallel(), or
  // produce_range() (one round at a time); then end().
  void begin(int64_t n_ots) { begin_batch_(n_ots); }

  void next(AuthValue *out) override {
    this->assert_in_session_();
    ensure_tree_available_();
    process_one_tree_(out);
  }

  void end() override {
    // All rounds were prepaid and the carry already rolled forward in begin();
    // nothing to ship or roll here (a following begin() continues the base /
    // inner-Ferret / counter chains from where this batch left them).
    this->exit_session_();
  }

  // Cursor-ordered bulk draw with the same auto-rollover semantics as next().
  // Splits each current-round slice across up to `n_threads` workers (n_threads
  // < 0 → constructor value). Mutates the cursor; not concurrent with
  // next()/produce_range() on the same instance.
  void next_chunks_parallel(AuthValue *out, int64_t n_chunks,
                            int n_threads = -1) {
    this->assert_in_session_();
    if (n_chunks <= 0) return;
    const int T = (n_threads < 0) ? n_threads_ : n_threads;
    const int64_t chunk = this->chunk_size();
    if (T <= 1) {
      for (int64_t i = 0; i < n_chunks; ++i) next(out + i * chunk);
      return;
    }
    int64_t done = 0;
    std::vector<std::thread> ths;
    ths.reserve((size_t)T);
    while (done < n_chunks) {
      ensure_tree_available_();
      const int64_t avail = round_capacity() - local_tree_;
      const int64_t take  = std::min<int64_t>(avail, n_chunks - done);
      const int64_t base_tree = local_tree_;
      ths.clear();
      const int64_t per = (take + T - 1) / T;
      for (int t = 0; t < T; ++t) {
        const int64_t tree_begin = base_tree + t * per;
        if (tree_begin >= base_tree + take) break;
        const int64_t count =
            std::min<int64_t>(per, base_tree + take - tree_begin);
        AuthValue *dst = out + (done + (tree_begin - base_tree)) * chunk;
        ths.emplace_back([this, dst, tree_begin, count]() {
          produce_range(dst, tree_begin, count);
        });
      }
      for (auto &th : ths) th.join();
      local_tree_ += take;
      done += take;
    }
  }

  // Thread-safe, index-addressed batch produce within the *current* round:
  // writes trees [tree_begin, tree_begin + n_trees) into `out` (out + m*chunk =
  // tree tree_begin+m), wire-free. Callers may invoke it concurrently with
  // disjoint ranges and disjoint `out`; output is order/thread-independent and
  // bit-identical to the serial next() path. Within one round use EITHER
  // produce_range OR the cursor (next/run/next_n); to span rounds, drive the
  // cursor (which rolls wire-free).
  void produce_range(AuthValue *out, int64_t tree_begin,
                     int64_t n_trees) const {
    assert(tree_begin >= 0 && n_trees >= 0 &&
           tree_begin + n_trees <= round_capacity() &&
           "produce_range out of current-round bounds");
    produce_trees_(out, abs_round_base_ + (uint64_t)consume_round_,
                   consume_round_, tree_begin, n_trees);
  }

 protected:
  void process_one_tree_(AuthValue *out) override {
    produce_trees_(out, abs_round_base_ + (uint64_t)consume_round_,
                   consume_round_, local_tree_, 1);
    local_tree_++;
  }

 private:
  // Prepay K = ceil(n_ots / cpr) rounds: ship every round's RCOT pull +
  // corrections, fold the batched-check accumulators, retain per-round state for
  // the wire-free consume, and roll the carry forward — then one batched check.
  void begin_batch_(int64_t n_ots) {
    this->enter_session_();
    const bool need_swap = !this->setup_done;
    this->bootstrap_();                          // first call fills carry_next_
    if (need_swap) std::swap(this->carry_curr_, this->carry_next_);

    if (n_threads_ > 1 && !pool_)
      pool_ = std::make_unique<ThreadPool>((size_t)n_threads_);

    const int64_t t  = this->param.t;
    const int64_t td = this->param.tree_depth;
    const int64_t cpr = cots_per_round();
    const int64_t K = (n_ots <= 0) ? 1 : (n_ots + cpr - 1) / cpr;
    n_rounds_       = K;
    batch_n_ots_    = (n_ots <= 0) ? cpr : n_ots;
    abs_round_base_ = abs_round_;

    carry_store_.resize((size_t)K * M_);
    if (!this->is_delta_holder()) {
      base_store_.resize((size_t)K * t * td);
      c_store_.resize((size_t)K * t * td);
      ss_store_.resize((size_t)K * t);
    } else {
      seed_scratch_.resize(t);
      gamma_scratch_.resize(t);
    }
    triple_scratch_.resize(t);

    acc_vb_    = AuthValue::f_zero();
    acc_xstar_ = AuthValue::f_zero();
    acc_va_    = AuthValue::f_zero();

    for (int64_t r = 0; r < K; ++r) {
      const uint64_t abs = abs_round_base_ + (uint64_t)r;
      this->inner_run_begin_();                  // pull base COTs + gadget begin

      if (this->is_delta_holder() && !cggm_seed_key_set_) {
        cggm_seed_key_     = this->gadget_send_->prg.seed();
        cggm_seed_key_set_ = true;
      }
      if (!lpn_key_set_) {
        lpn_key_     = this->lpn_->prg_key();
        lpn_key_set_ = true;
      }

      // Retain this round's base COTs (receiver re-evals against them).
      if (!this->is_delta_holder())
        std::copy(this->base_cots_.begin(), this->base_cots_.end(),
                  base_store_.begin() + (size_t)r * t * td);

      // Ship this round's corrections / secret_sums (folds VW into the gadget).
      if (this->is_delta_holder()) {
        PRG sp(&cggm_seed_key_);
        sp.seek(abs * (uint64_t)t);
        sp.random_block(seed_scratch_.data(), t);
        for (int64_t i = 0; i < t; ++i)
          gamma_scratch_[i] = this->carry_curr_[i].mac;
        this->gadget_send_->prepare_all(pool_.get(), batch_,
                                        this->base_cots_.data(),
                                        seed_scratch_.data(),
                                        gamma_scratch_.data());
      } else {
        for (int64_t i = 0; i < t; ++i)
          triple_scratch_[i] = this->carry_curr_[i].mac;
        this->gadget_recv_->prepare_all(
            pool_.get(), batch_, this->base_cots_.data(),
            c_store_.data() + (size_t)r * t * td, triple_scratch_.data(),
            ss_store_.data() + (size_t)r * t);
      }

      // Snapshot the round's carry triples [0, M) for the wire-free produce.
      std::copy(this->carry_curr_.begin(), this->carry_curr_.begin() + M_,
                carry_store_.begin() + (size_t)r * M_);

      // Fold this round's contribution into the batched FTyped check.
      if (this->is_delta_holder())
        this->gadget_send_->fold_round_check_typed(acc_vb_,
                                                   this->carry_curr_[t]);
      else
        this->gadget_recv_->fold_round_check_typed(
            acc_xstar_, acc_va_, this->carry_curr_.data(),
            this->carry_curr_[t]);

      // Roll the carry forward wire-free: this round's refill trees produce the
      // next round's carry. swap so carry_curr_ becomes round r+1 (= the next
      // batch's round 0 after the final iteration).
      produce_trees_(this->carry_next_.data(), abs, r, round_capacity(),
                     this->param.refill_trees);
      std::swap(this->carry_curr_, this->carry_next_);
    }

    // One check over the whole prepay (m = K*t trees). K=1 is byte-identical to
    // run_end_typed, so a no-arg SilentSvole stays wire-equivalent to Svole.
    if (this->is_delta_holder())
      this->gadget_send_->finalize_batched_typed_sender(acc_vb_);
    else
      this->gadget_recv_->finalize_batched_typed_receiver(acc_xstar_, acc_va_);

    abs_round_     = abs_round_base_ + (uint64_t)K;
    consume_round_ = 0;
    local_tree_    = 0;
  }

  // If the cursor has consumed the round's user budget, roll to the next
  // prepaid round wire-free, or live end()+begin() once the batch is exhausted.
  void ensure_tree_available_() {
    if (local_tree_ != round_capacity()) return;
    if (consume_round_ + 1 < n_rounds_) {
      consume_round_++;
      local_tree_ = 0;
    } else {
      end();
      begin(batch_n_ots_);
    }
  }

  // Produce `n` consecutive trees [local_begin, local_begin + n) of absolute
  // round `abs_round` (batch-local index `store_round`) into `out`. Reads only
  // the per-round stores + the deterministic re-derivation keys; no wire I/O and
  // no shared mutable state (own scratch per call) → thread-safe / const.
  void produce_trees_(AuthValue *out, uint64_t abs_round, int64_t store_round,
                      int64_t local_begin, int64_t n) const {
    const int64_t chunk = this->chunk_size();
    const int64_t td = this->param.tree_depth;
    const int64_t t  = this->param.t;
    const AuthValue *carry = carry_store_.data() + (size_t)store_round * M_;
    const AuthValue *pre   = carry + t;          // LPN secret region [t, t+k]

    const uint64_t G0 = abs_round * (uint64_t)t + (uint64_t)local_begin;
    PRG lpn_prg(&lpn_key_);
    lpn_prg.seek(G0 * bpc_);
    PRG seed_prg(&cggm_seed_key_);               // sender only
    const bool holder = this->is_delta_holder();
    if (holder) seed_prg.seek(G0);

    const block *base_r = holder ? nullptr
                                 : base_store_.data() + (size_t)store_round * t * td;
    const block *c_r    = holder ? nullptr
                                 : c_store_.data() + (size_t)store_round * t * td;
    const F     *ss_r   = holder ? nullptr
                                 : ss_store_.data() + (size_t)store_round * t;

    std::vector<block> leaf_scr(leave_n_);       // cGGM block sink (per call)
    block kr_scr[kMaxTreeDepth];                 // k0 (sender) / kr (receiver)

    for (int64_t m = 0; m < n; ++m) {
      const int64_t L = local_begin + m;
      AuthValue *dst = out + m * chunk;
      if (holder) {
        block seed;
        seed_prg.random_block(&seed, 1);
        this->gadget_send_->produce_tree(dst, seed, kr_scr, leaf_scr.data());
      } else {
        const uint32_t rev = this->gadget_recv_->produce_tree(
            dst, base_r + L * td, c_r + L * td, kr_scr, leaf_scr.data(),
            ss_r[L], carry[L].mac);
        dst[rev].val = carry[L].val;             // α-slot val from the carry
      }
      this->lpn_->compute_slice(lpn_prg, dst, pre, chunk);
    }
  }

  int n_threads_ = 1;
  int batch_     = 1;
  int64_t leave_n_ = 0;
  int64_t M_ = 0;                                // svole_M(param): carry width
  uint64_t bpc_ = 0;                             // LPN PRG blocks per chunk
  std::unique_ptr<ThreadPool> pool_;             // null when n_threads_ <= 1

  // Deterministic re-derivation keys (captured on first begin()).
  block lpn_key_;       bool lpn_key_set_       = false;
  block cggm_seed_key_; bool cggm_seed_key_set_ = false;

  // Prepaid-batch state.
  int64_t  n_rounds_       = 1;                  // K rounds prepaid by last begin
  int64_t  batch_n_ots_    = 0;                  // re-prepaid on live rollover
  uint64_t abs_round_      = 0;                  // running absolute round
  uint64_t abs_round_base_ = 0;                  // abs index of this batch round 0
  int64_t  consume_round_  = 0;                  // batch-local round in [0,K)
  int64_t  local_tree_     = 0;                  // user tree within the round

  // Per-round retained state (K rounds). Receiver keeps the base COTs,
  // corrections, and secret_sums it cannot re-derive; both roles keep the
  // carry triples [0,M) per round. Sender re-derives seeds from cggm_seed_key_.
  std::vector<block>     base_store_;            // K * t * tree_depth (receiver)
  std::vector<block>     c_store_;               // K * t * tree_depth (receiver)
  std::vector<F>         ss_store_;              // K * t (receiver)
  std::vector<AuthValue> carry_store_;           // K * M

  // Per-round scratch.
  std::vector<block> seed_scratch_;              // t (sender)
  std::vector<F>     gamma_scratch_;             // t (sender)
  std::vector<F>     triple_scratch_;            // t

  // Batched FTyped check accumulators (one F each, folded incrementally).
  F acc_vb_    = AuthValue::f_zero();            // sender δ-free running sum
  F acc_xstar_ = AuthValue::f_zero();            // receiver Σ x_star_r
  F acc_va_    = AuthValue::f_zero();            // receiver running va
};

// Convenience aliases mirroring F2kVOLE / FpVOLE.
template <typename AuthValue = AuthValueF2k>
using SilentF2kVOLE = SilentSvole<AuthValue>;
template <typename AuthValue = AuthValueFp>
using SilentFpVOLE = SilentSvole<AuthValue>;

}  // namespace emp
#endif  // EMP_OT_SVOLE_SILENT_SVOLE_H__
