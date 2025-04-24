#include "user.hpp"
#include "hash.hpp"
#include "random.hpp"
#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <nlohmann/json.hpp> // 引入 nlohmann/json 库
#include <cstring> // 包含字符串处理函数的头文件
using json = nlohmann::json;

/**
 * pk_sharing: K-1 elements
 */
void inline key_rerandomization(const context *ctx, publickey *pk_sharing,
		G1 *h, G1 agg_sig, publickey *pk_sharing_new, G1 &agg_sig_new) {

	//sample a random sharing of zero
	Fr sharing_offsets[PAR_K];
	sharing_offsets[0].setRand();
	sharing_offsets[PAR_K - 1] = sharing_offsets[0];
	for (int i = 1; i < PAR_K - 1; ++i) {
		sharing_offsets[i].setRand();
		Fr::add(sharing_offsets[PAR_K - 1], sharing_offsets[PAR_K - 1],
				sharing_offsets[i]);

	}
	Fr::neg(sharing_offsets[PAR_K - 1], sharing_offsets[PAR_K - 1]);

	//shift the public key shares
	G1 tmp1;
	G2 tmp2;
	for (int i = 0; i < PAR_K - 1; ++i) {
		G1::mul(tmp1, ctx->g1, sharing_offsets[i]);
		G1::add(pk_sharing_new[i].pk1, pk_sharing[i].pk1, tmp1);
		G2::mul(tmp2, ctx->g2, sharing_offsets[i]);
		G2::add(pk_sharing_new[i].pk2, pk_sharing[i].pk2, tmp2);
	}

	//shift agg sig
	G1 shift;
	G1::mulVec(shift, h, sharing_offsets, PAR_K);
	G1::add(agg_sig_new, agg_sig, shift);

}

void user_challenge(const context *ctx, const publickey *pk,
		const unsigned char *info, const unsigned char *messagedigest,
		user_state *state, challenge *chall) {

	// save pk and ctx for later
	//std::cout << "start user_chanllenge " << std::endl;
	state->pk = pk;
	state->ctx = ctx;

	// some tmp element for computation
	G1 g1alpha;
	//std::cout << "g1alpha" << std::endl;
	unsigned char rand[PAR_K * PAR_N * PAR_L* 2 * SECPAR];
	unsigned char com[PAR_K * PAR_N * SECPAR];
	//std::cout << "define rand com " << std::endl;

	// prepare mu's, alpha's, com's, c's
	// for every instance and every session and every message
	for (int i = 0; i < PAR_K; ++i) {
		for (int j = 0; j < PAR_N; ++j) {
			int idx = (i * PAR_N) + j;
			for(int l = 0;l < PAR_L; ++l){
				int idx_r = (i * PAR_N + j) * PAR_L + l;    
				//std::cout << "idx_r " <<idx_r<<  std::endl;                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
				// sample varphi_{i,j,l}
				random_bytes(&state->varphis[idx_r * SECPAR], SECPAR);
				//std::cout << "random_bytes " << std::endl;
				// compute mu_{i,j,l}
				hash_mu(messagedigest, &state->varphis[idx_r * SECPAR],
						&rand[idx * (PAR_L+ 1)* SECPAR  + l * SECPAR ]);
			}
			//sample gamma_{i,j} next to it
			random_bytes(&rand[ (idx+1)*(PAR_L+1) * SECPAR - SECPAR], SECPAR);

			// compute com_{i,j}
			hash_r(&rand[idx * (PAR_L + 1) * SECPAR], PAR_L , &com[idx * SECPAR]);
			//std::cout << "hash_r " << std::endl;
			// compute alpha_{i,j,l}  
			for(int p = 0;p < PAR_L;++p){
				int idx_p = (i * PAR_N + j) * PAR_L + p;
				hash_alpha(&rand[(idx+1)*(PAR_L+1) * SECPAR - SECPAR], p, state->alphas[idx_p]);
			}

			// compute c_{i,j,l}
			for(int c = 0;c < PAR_L;++c){
				int idx_c = (i * PAR_N + j) * PAR_L + c;
				hash_bls(&rand[idx * (PAR_L+ 1)* SECPAR  + c * SECPAR ], info, state->mu_hashes[idx_c]);
				//std::cout << "hash_bls " << std::endl;
				G1::mul(g1alpha, ctx->g1, state->alphas[idx_c]);
				G1::add(state->c[idx_c], state->mu_hashes[idx_c], g1alpha);
			}	
		}
	}
	//std::cout << "first loop over " << std::endl;

	// hash to get the CC vector J
	hash_cc(com, state->c, PAR_L, chall->J);
	//std::cout << "hash_cc " << std::endl;
	// construct the challenge/opening and the user state
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];     
		int idx = i * PAR_N + Ji;                                                            
		int idx_c = (i * PAR_N + Ji) * PAR_L;
		//include c_{i,J_i,l} and com_{i,J_i}
		for(int l = 0; l < PAR_L; ++l){
			//int idx_c = (i * PAR_N  + Ji) * PAR_L;
			chall->c[i][l] = state->c[idx_c + l];
		}

		memcpy(&chall->com[i * SECPAR], &com[idx * SECPAR], SECPAR);
		//std::cout << "chall->com over " << std::endl;
		//include all rands except the J_i-th one
		memcpy(&chall->rand[i * (PAR_N - 1) * (PAR_L + 1) * SECPAR],
				&rand[i * PAR_N * (PAR_L + 1) * SECPAR], Ji * (PAR_L + 1) * SECPAR);
				//std::cout << "rand to chall_rand 1 " << i << std::endl;
		memcpy(&chall->rand[i * (PAR_N - 1) * (PAR_L + 1) * SECPAR + Ji * (PAR_L + 1) * SECPAR],
				&rand[(i * PAR_N + Ji + 1) * (PAR_L + 1) * SECPAR],
				(PAR_N - 1 - Ji) * (PAR_L + 1) * SECPAR);
				//std::cout << "rand to chall_rand 2 " << i <<std::endl;
	}
	std::cout << "second loop over " << std::endl;

}

bool user_finalize(user_state *state, challenge *chall, response *resp,
		signature &sig) {

	// Step 1: Recompute final component pk_K of the sharing
	std::cout << "user_finalize start " << std::endl;
	G1 pk_sharing_G1[PAR_K];
	G2 pk_sharing_G2[PAR_K + 1]; //one more element to make Step 3 efficient
	G1 sum_G1;
	G2 sum_G2;
	pk_sharing_G1[0] = resp->pk_sharing[0].pk1;
	pk_sharing_G2[0] = resp->pk_sharing[0].pk2;
	sum_G1 = pk_sharing_G1[0];
	sum_G2 = pk_sharing_G2[0];
	for (int i = 1; i < PAR_K - 1; ++i) {
		pk_sharing_G1[i] = resp->pk_sharing[i].pk1;
		pk_sharing_G2[i] = resp->pk_sharing[i].pk2;
		G1::add(sum_G1, sum_G1, pk_sharing_G1[i]);
		G2::add(sum_G2, sum_G2, pk_sharing_G2[i]);
	}
	G1::neg(sum_G1, sum_G1);
	G1::add(pk_sharing_G1[PAR_K - 1], state->pk->pk1, sum_G1);
	G2::neg(sum_G2, sum_G2);
	G2::add(pk_sharing_G2[PAR_K - 1], state->pk->pk2, sum_G2);

	// Step 2: Check validity of the sharing
	bool consistent = true;
	GT tmp;
	G1 left[2];
	G2 right[2];
	G1::neg(left[1], state->ctx->g1);
	right[0] = state->ctx->g2;
	for (int i = 0; i < PAR_K; ++i) {
		//check that e(pk_i,1,g_2) = e(g_1,pk_i,2)
		left[0] = pk_sharing_G1[i];
		right[1] = pk_sharing_G2[i];
		millerLoopVec(tmp, left, right, 2);
		finalExp(tmp, tmp);
		consistent &= tmp.isOne();
	}
	if (!consistent) {
		return false;
	}

	// Step 3: Check correctness of the aggregated response
	G1 cs_and_add_resp[PAR_L][PAR_K + 1];
	for (int l = 0; l < PAR_L; ++l){
		G1::neg(cs_and_add_resp[l][PAR_K], resp->agg_resp[l]);
		for (int i = 0; i < PAR_K; ++i) {
			cs_and_add_resp[l][i] = chall->c[i][l];
		}
	} 
	//G1::neg(cs_and_add_resp[PAR_K], resp->agg_resp);
	pk_sharing_G2[PAR_K] = state->ctx->g2;
	for (int l = 0; l < PAR_L; ++l){
		millerLoopVec(tmp, cs_and_add_resp[l], pk_sharing_G2, PAR_K + 1);
		finalExp(tmp, tmp);
		if (!tmp.isOne()) {
			return false;
		}
	}
	//millerLoopVec(tmp, cs_and_add_resp, pk_sharing_G2, PAR_K + 1);
	//finalExp(tmp, tmp);
	//if (!tmp.isOne()) {
	//	return false;
	//}

	// Step 4: Unblind the aggregated response
	G1 agg_sig[PAR_L];
	G1 shift[PAR_L];
	Fr neg_alphas[PAR_L][PAR_K];
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];
		int idx = (i * PAR_N + Ji) * PAR_L;
		for (int l = 0; l < PAR_L; ++l){
			Fr::neg(neg_alphas[l][i], state->alphas[idx+l]);
		}
	}
	for (int l = 0; l < PAR_L; ++l){
		G1::mulVec(shift[l], pk_sharing_G1, neg_alphas[l], PAR_K);
		G1::add(agg_sig[l], resp->agg_resp[l], shift[l]);
	}
	//G1::mulVec(shift, pk_sharing_G1, neg_alphas, PAR_K);
	//G1::add(agg_sig, resp->agg_resp, shift);
	//Rerandomize the key sharing 
	G1 selected_mu_hashes[PAR_L][PAR_K];
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];
		int idx = (i * PAR_N + Ji) * PAR_L;
		for (int l = 0; l < PAR_L; ++l){
			selected_mu_hashes[l][i] = state->mu_hashes[idx+l];
		}
	}
	for (int l = 0; l < PAR_L; ++l){
		key_rerandomization(state->ctx, resp->pk_sharing, selected_mu_hashes[l],
			agg_sig[l], sig.pk_sharing, sig.agg_sig[l]);
	}

	// Step 5: add the commitment randomness the signature
	for (int i = 0; i < PAR_K; ++i) {
		int Ji = chall->J[i];
		int idx = (i * PAR_N + Ji) * PAR_L;
		for (int l = 0; l < PAR_L; ++l){
			memcpy(&sig.com_rands[i * SECPAR ][l * SECPAR], &state->varphis[(idx + l) * SECPAR],
		SECPAR);
		}
	}
	std::cout << "user_finalize over 1 " << std::endl;
	std::ofstream outFile("datsignature.bin.new", std::ios::binary);
    if (outFile) {
        outFile.write(reinterpret_cast<const char*>(&sig), sizeof(sig));
        outFile.close();
    } else {
        std::cerr << "无法打开文件进行写入" << std::endl;
    }
	std::cout << "user_finalize over 2  file make  " << std::endl;
	return true;
}
