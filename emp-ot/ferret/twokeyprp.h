#ifndef EMP_FERRET_TWO_KEY_PRP_H__
#define EMP_FERRET_TWO_KEY_PRP_H__

#include "emp-tool/emp-tool.h"
using namespace emp;

//kappa->2kappa PRG, implemented as G(k) = PRF_seed0(k)\xor k || PRF_seed1(k)\xor k
class TwoKeyPRP { public:
	AES_KEY aes_key[2];

	TwoKeyPRP(block seed0, block seed1) {
	  AES_set_encrypt_key((const block)seed0, aes_key);
	  AES_set_encrypt_key((const block)seed1, &aes_key[1]);
	}

	void node_expand_1to2(block *children, block parent) {
	  block tmp[2];
	  tmp[0] = children[0] = parent;
	  tmp[1] = children[1] = parent;
	  permute_block_2blks(tmp);
	  children[0] = children[0] ^ tmp[0];
	  children[1] = children[1] ^ tmp[1];
	}

	void node_expand_2to4(block *children, block *parent) {
	  block tmp[4];
	  tmp[3] = children[3] = parent[1];
	  tmp[2] = children[2] = parent[1];
	  tmp[1] = children[1] = parent[0];
	  tmp[0] = children[0] = parent[0];
	  permute_block_4blks(tmp);
	  children[3] = children[3] ^ tmp[3];
	  children[2] = children[2] ^ tmp[2];
	  children[1] = children[1] ^ tmp[1];
	  children[0] = children[0] ^ tmp[0];
	}

	inline void
	__attribute__((target("aes,sse2")))
	permute_block_4blks(block *blks) {
	  blks[0] = _mm_xor_si128(blks[0], aes_key[0].rd_key[0]);
	  blks[1] = _mm_xor_si128(blks[1], aes_key[1].rd_key[0]);
	  blks[2] = _mm_xor_si128(blks[2], aes_key[0].rd_key[0]);
	  blks[3] = _mm_xor_si128(blks[3], aes_key[1].rd_key[0]);
	  for (unsigned int j = 1; j < aes_key[0].rounds; ++j) {
			blks[0] = _mm_aesenc_si128(blks[0], aes_key[0].rd_key[j]);
			blks[2] = _mm_aesenc_si128(blks[2], aes_key[0].rd_key[j]);
	  }
	  for (unsigned int j = 1; j < aes_key[1].rounds; ++j) {
			blks[1] = _mm_aesenc_si128(blks[1], aes_key[1].rd_key[j]);
			blks[3] = _mm_aesenc_si128(blks[3], aes_key[1].rd_key[j]);
	  }
	  blks[0] = _mm_aesenclast_si128(blks[0], aes_key[0].rd_key[aes_key[0].rounds]);
	  blks[1] = _mm_aesenclast_si128(blks[1], aes_key[1].rd_key[aes_key[1].rounds]);
	  blks[2] = _mm_aesenclast_si128(blks[2], aes_key[0].rd_key[aes_key[0].rounds]);
	  blks[3] = _mm_aesenclast_si128(blks[3], aes_key[1].rd_key[aes_key[1].rounds]);
	}

	inline void
	__attribute__((target("aes,sse2")))
	permute_block_2blks(block *blks) {
	  blks[0] = _mm_xor_si128(blks[0], aes_key[0].rd_key[0]);
	  blks[1] = _mm_xor_si128(blks[1], aes_key[1].rd_key[0]);
	  for (unsigned int j = 1; j < aes_key[0].rounds; ++j)
			blks[0] = _mm_aesenc_si128(blks[0], aes_key[0].rd_key[j]);
	  for (unsigned int j = 1; j < aes_key[1].rounds; ++j)
			blks[1] = _mm_aesenc_si128(blks[1], aes_key[1].rd_key[j]);
	  blks[0] = _mm_aesenclast_si128(blks[0], aes_key[0].rd_key[aes_key[0].rounds]);
	  blks[1] = _mm_aesenclast_si128(blks[1], aes_key[1].rd_key[aes_key[1].rounds]);
	}
};
#endif
