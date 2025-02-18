#include "signer.hpp"
#include "hash.hpp"
#include <iostream>
#include <omp.h>


bool inline sanity_check(const context *ctx, const unsigned char *info, const challenge *chall) {
	// recompute the set of challenges, and all commitments
	std::cout << "ctx " << ctx << std::endl;
	std::cout << "info " << info << std::endl;
	std::cout << "chall " << chall << std::endl;
	G1 c[PAR_K * PAR_N * PAR_L];
	unsigned char com[PAR_K * PAR_N * SECPAR];

	Fr alpha;
	G1 g1alpha;
	G1 hash_mu;
	std::cout << "info " << info << std::endl;

	// Parallelize the outer loop over PAR_K
	#pragma omp parallel for private(alpha, g1alpha, hash_mu)
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];
		// the values left of Ji
		for (int j = 0; j < Ji; ++j) {
			int idx_dst = i * PAR_N + j;
			int idx_src = i * (PAR_N - 1) + j;
			// hash rand to get com
			hash_r(&chall->rand[idx_src * (PAR_L + 1) * SECPAR], PAR_L, &com[idx_dst * SECPAR]);

			// hash gamma (second part of rand) to get alpha
			for (int l = 0; l < PAR_L; ++l) {
				int idx_l = (i * (PAR_N - 1) + j) * PAR_L + l;
				hash_alpha(&chall->rand[(idx_src + 1) * (PAR_L + 1) * SECPAR - SECPAR], l, alpha);
				hash_bls(&chall->rand[idx_src * (PAR_L + 1) * SECPAR + l * PAR_L], info, hash_mu);
				G1::mul(g1alpha, ctx->g1, alpha);
				G1::add(c[idx_l], hash_mu, g1alpha);
			}
		}

		// copy the Ji-th commitment and challenge
		memcpy(&com[(i * PAR_N + Ji) * SECPAR], &chall->com[i * SECPAR], SECPAR);

		for (int l = 0; l < PAR_L; ++l) {
			c[(i * PAR_N + Ji) * PAR_L + l] = chall->c[l][i];
		}

		// the values right of Ji
		for (int j = Ji + 1; j < PAR_N; ++j) {
			int idx_dst = i * PAR_N + j;
			int idx_src = i * (PAR_N - 1) + j - 1;
			// hash rand to get com
			hash_r(&chall->rand[idx_src * (PAR_L + 1) * SECPAR], PAR_L, &com[idx_dst * SECPAR]);

			// hash gamma (second part of rand) to get alpha
			for (int l = 0; l < PAR_L; ++l) {
				int idx_l = (i * PAR_N + j) * PAR_L + l;
				hash_alpha(&chall->rand[(idx_src + 1) * (PAR_L + 1) * SECPAR - SECPAR], l, alpha);
				hash_bls(&chall->rand[idx_src * (PAR_L + 1) * SECPAR + l * PAR_L], info, hash_mu);
				G1::mul(g1alpha, ctx->g1, alpha);
				G1::add(c[idx_l], hash_mu, g1alpha);
			}
		}
	}

	return true;
}


bool inline sanity_check_not_optimize(const context *ctx, const unsigned char *info,
		const challenge *chall) {
	//recompute the set of challenges, and all commitments
	std::cout << "ctx " << ctx <<std::endl;
	std::cout << "info " << info <<std::endl;
	std::cout << "chall " << chall <<std::endl;
	G1 c[PAR_K * PAR_N * PAR_L];
	unsigned char com[PAR_K * PAR_N * SECPAR];

	Fr alpha;
	G1 g1alpha;
	G1 hash_mu;
	std::cout << "info " << info <<std::endl;
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];
		//the values left of Ji
		for (int j = 0; j < Ji; ++j) {
			int idx_dst = i * PAR_N + j;
			int idx_src = i * (PAR_N - 1) + j;
			//hash rand to get com
			hash_r(&chall->rand[idx_src * (PAR_L + 1) * SECPAR], PAR_L,
					&com[idx_dst * SECPAR]);
			//hash gamma (second part of rand) to get alpha
			for (int l = 0; l < PAR_L; ++l){
				int idx_l = (i * (PAR_N - 1)  + j) * PAR_L + l;
				//这里α算出来可能会有问题,因为l可能不一样
				hash_alpha(&chall->rand[(idx_src+1)*(PAR_L+1) * SECPAR - SECPAR] , l, alpha);
				hash_bls(&chall->rand[idx_src * (PAR_L + 1) * SECPAR + l * PAR_L], info, hash_mu);
				G1::mul(g1alpha, ctx->g1, alpha);
				G1::add(c[idx_l], hash_mu, g1alpha);
			}
			//hash_alpha(&chall->rand[idx_src * 2 * SECPAR + SECPAR], 0, alpha);
			//compute c_i,j by hashing mu (first part of rand) and info
			//and shifting by g_1alpha
			//hash_bls(&chall->rand[idx_src * 2 * SECPAR], info, hash_mu);
			//G1::mul(g1alpha, ctx->g1, alpha);
			//G1::add(c[idx_dst], hash_mu, g1alpha);

		}
		//copy the Ji-th commitment and challenge
		memcpy(&com[(i * PAR_N + Ji) * SECPAR], &chall->com[i * SECPAR],
		SECPAR);
		//这里可能有问题
		for (int l = 0; l < PAR_L; ++l){
			c[(i * PAR_N + Ji) * PAR_L + l] = chall->c[l][i];
		}
		//c[i * PAR_N * PAR_L+ Ji] = chall->c[i];
		//the values right of Ji
		for (int j = Ji + 1; j < PAR_N; ++j) {
			int idx_dst = i * PAR_N + j;
			int idx_src = i * (PAR_N - 1) + j - 1;
			//hash rand to get com
			hash_r(&chall->rand[idx_src * (PAR_L + 1) * SECPAR],PAR_L,
					&com[idx_dst * SECPAR]);
			//hash gamma (second part of rand) to get alpha
			for (int l = 0; l < PAR_L; ++l){
				int idx_l = (i * PAR_N  + j) * PAR_L + l;
				hash_alpha(&chall->rand[(idx_src+1)*(PAR_L+1) * SECPAR - SECPAR] , l, alpha);
				hash_bls(&chall->rand[idx_src * (PAR_L + 1) * SECPAR + l * PAR_L], info, hash_mu);
				G1::mul(g1alpha, ctx->g1, alpha);
				G1::add(c[idx_l], hash_mu, g1alpha);
			}
			//hash_alpha(&chall->rand[idx_src * 2 * SECPAR + SECPAR], 0, alpha);
			//compute c_i,j by hashing mu (first part of rand) and info
			//and shifting by g_1alpha
			//hash_bls(&chall->rand[idx_src * 2 * SECPAR], info, hash_mu);
			//G1::mul(g1alpha, ctx->g1, alpha);
			//G1::add(c[idx_dst], hash_mu, g1alpha);
		}
	}
	std::cout << "info " << info <<std::endl;

	//re-hash to get J
	uint32_t J[PAR_K];
	hash_cc(com, c, PAR_L, J);

	//check if J is equal to the J that the user sent
	for (int i = 0; i < PAR_K; ++i) {
		if (J[i] != chall->J[i]) {
			return false;
		}
	}
	return true;
}

bool signer(const context *ctx, const publickey *pk, const secretkey *sk,
		const unsigned char *info, const challenge *chall, response *resp) {
	// Verify the challenge
	if (!sanity_check(ctx, info, chall)) {
		return false;
	}

	// Sample a random key sharing
	Fr sk_sharing[PAR_K];
	Fr sum;
	G1 sum_s;
	sk_sharing[0].setRand();
	sum = sk_sharing[0];
	G1::mul(resp->pk_sharing[0].pk1, ctx->g1, sk_sharing[0]);
	G2::mul(resp->pk_sharing[0].pk2, ctx->g2, sk_sharing[0]);
	for (int i = 1; i < PAR_K - 1; ++i) {
		sk_sharing[i].setRand();
		Fr::add(sum, sum, sk_sharing[i]);
		G1::mul(resp->pk_sharing[i].pk1, ctx->g1, sk_sharing[i]);
		G2::mul(resp->pk_sharing[i].pk2, ctx->g2, sk_sharing[i]);
	}
	Fr::neg(sum, sum);
	Fr::add(sk_sharing[PAR_K - 1], sk->sk, sum);

	// Compute the aggregated response
	for (int l = 0; l < PAR_L ; ++l) {
		//for (int i = 0; i < (PAR_K - 1); ++i){
		//	G1::mul(resp->agg_resp[l], sk_sharing[i], chall->c[i][l]);
		//	G1::mul(sum_s, sk_sharing[i+1], chall->c[i+1][l]);
		//	G1::add(resp->agg_resp[l], resp->agg_resp[l], sum_s);
		//}
		G1::mulVec(resp->agg_resp[l], chall->c[l], sk_sharing, PAR_K);
	}
	//G1::mulVec(resp->agg_resp, chall->c, sk_sharing, PAR_K);
	return true;
}
