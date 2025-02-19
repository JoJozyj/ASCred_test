use ark_std::time::{Duration, Instant};
extern crate num_bigint;
use num_bigint::{BigInt, BigUint};
use ark_ff::{AdditiveGroup, BigInteger, Field, Fp, Fp2ConfigWrapper, MontBackend, PrimeField, QuadExtField, ToConstraintField};
use ark_ec::{pairing::{self, Pairing, PairingOutput}, AffineRepr, CurveGroup, PrimeGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, CanonicalSerializeHashExt, Compress,Validate, SerializationError};
// Bring in some tools for using pairing-friendly curves
// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use ark_bls12_381::{Bls12_381, G1Projective,Fr,G2Projective,G1Affine,G2Affine,Fq,FqConfig,Fq2Config,Fq2}; 
use ark_crypto_primitives::snark::{CircuitSpecificSetupSNARK, SNARK};
// We'll use these interfaces to construct our circuit.
use ark_relations::{
    lc, ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, Variable},
};
use ark_std::{Zero, UniformRand, ops::Mul};
use ark_std::hash::DefaultHasher;
use ark_std::test_rng;
// For randomness (during paramgen and proof generation)
use ark_std::rand::{Rng, RngCore, SeedableRng};
use ark_std::io;
use ark_std::rand::thread_rng;

use num_traits::MulAdd;
use sigma0_polymath::{
    blake3::Blake3Transcript, keccak256::Keccak256Transcript, merlin::MerlinFieldTranscript,
    Polymath, Transcript,
};
use std::{borrow::Borrow, hash::Hash, io::Cursor};
use sha2::{Sha256, Digest};
use std::marker::PhantomData;

use std::fs::File;
use std::io::Read;
use std::path::Path;
use std::mem;
type MyField = Fp<MontBackend<FqConfig, 4>, 4>;
struct RaichooSigCircuit<F:Field> {
    sigma: G1Projective,
    g2: G2Projective,
    tmp_left: PairingOutput<Bls12_381>,
    sigma_scar: G1Projective,
    g2_scar:G2Projective,
    tmp_right: PairingOutput<Bls12_381>,

    _marker: PhantomData<F>, 
}

impl<> ConstraintSynthesizer<Fr> for RaichooSigCircuit<Fr> {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {

        let b: Fp<MontBackend<ark_bls12_381::FrConfig, 4>, 4> = Fp::ONE;
        println!("b:{b}");
        let b_var = cs.new_input_variable(|| Ok(b))?;

        // 计算右边的配对
        let mut bufferright_e = Vec::new();
        let mut writerright_e = Cursor::new(&mut bufferright_e);
        let right_sesult_e = Bls12_381::pairing(self.sigma_scar, self.g2);
        println!("right_sesult_e:{:?}",right_sesult_e);
        let _ = right_sesult_e.serialize_with_mode(&mut writerright_e, Compress::No);
        
        let mut bufferright_out = Vec::new();
        let mut writerright_out = Cursor::new(&mut bufferright_out);
        let _ = self.tmp_right.serialize_with_mode(&mut writerright_out, Compress::No);

        // 计算左边的配对 e(σ, g2_scar)
        let mut bufferleft_e = Vec::new();
        let mut writerleft_e = Cursor::new(&mut bufferleft_e);
        let left_result_e = Bls12_381::pairing(self.sigma, self.g2_scar);
        println!("left_result_e:{:?}",left_result_e);
        let _ = left_result_e.serialize_with_mode(&mut writerleft_e, Compress::No);

        let mut bufferleft_out = Vec::new();
        let mut writerleft_out = Cursor::new(&mut bufferleft_out);
        let _ = self.tmp_left.serialize_with_mode(&mut writerleft_out, Compress::No);


        // 添加哈希约束
        let mut hasherleft_e = Sha256::new();
        hasherleft_e.update(&bufferleft_e);
        let hash_result_left_e = hasherleft_e.finalize();
        let hash_left_e = Fp::from_be_bytes_mod_order(&hash_result_left_e);
        println!("hash_left_e:{hash_left_e}");
        let cs_hash_left_e = cs.new_witness_variable(|| Ok(hash_left_e))?;

        let mut hasherleft_out = Sha256::new();
        hasherleft_out.update(&bufferleft_out);
        let hash_result_left_out = hasherleft_out.finalize();
        let hash_left_out = Fp::from_be_bytes_mod_order(&hash_result_left_out);
        println!("hash_left_out:{hash_left_out}");
        
        let cs_hash_left_out = cs.new_witness_variable(|| Ok(hash_left_out))?;
        
        //左边哈希约束
        
        cs.enforce_constraint(
            lc!() + cs_hash_left_e, 
            lc!() + b_var, 
            lc!() + cs_hash_left_out
        )?;
        
        //右边哈希约束

        let mut hasherright_e = Sha256::new();
        hasherright_e.update(&bufferright_e);
        let hash_result_right_e = hasherright_e.finalize();
        let hash_right_e = Fp::from_be_bytes_mod_order(&hash_result_right_e);
        println!("hash_right_e:{hash_right_e}");
        let cs_hash_right_e = cs.new_witness_variable(|| Ok(hash_right_e))?;

        let mut hasherright_out = Sha256::new();
        hasherright_out.update(&bufferright_out);
        let hash_result_right_out = hasherright_out.finalize();
        let hash_right_out = Fp::from_be_bytes_mod_order(&hash_result_right_out);
        println!("hash_right_out:{hash_right_out}");

        let cs_hash_right_out = cs.new_witness_variable(|| Ok(hash_right_out))?;
        
        cs.enforce_constraint(
            lc!() + cs_hash_right_e, 
            lc!() + b_var, 
            lc!() + cs_hash_right_out
        )?;
        

        // 添加配对相等约束 e(σ, g2) = tmp_left
        cs.enforce_constraint(
            lc!() + cs_hash_left_out, 
            lc!() + b_var, 
            lc!() + cs_hash_right_out
        )?;

        println!("bufferright_e{:?}",bufferright_e);
        println!("bufferright_out{:?}",bufferright_out);

        Ok(())
    }
}

fn bytes_to_g1_affine(bytes: &[u8]) -> Result<G1Affine, SerializationError> {
    // 使用 Cursor 将字节数据包装为 Reader
    let cursor = std::io::Cursor::new(bytes);
    
    // 使用反序列化方法读取 G1Affine
    let g1_affine = G1Affine::deserialize_with_mode(cursor, Compress::No, Validate::Yes)?;
    Ok(g1_affine.into())
}
fn bytes_to_g2_affine(bytes: &[u8]) -> Result<G2Affine, SerializationError> {
    // 使用 Cursor 将字节数据包装为 Reader
    let cursor = std::io::Cursor::new(bytes);
    
    // 使用反序列化方法读取 G2Affine
    let g2_affine = G2Affine::deserialize_with_mode(cursor, Compress::No, Validate::Yes)?;
    Ok(g2_affine.into())
}

fn bytes_to_pairing_output(bytes: &[u8]) -> Result<PairingOutput<Bls12_381>, SerializationError> {
    // 使用 Cursor 将字节数据包装为 Reader
    let cursor = std::io::Cursor::new(bytes);
    
    // 使用反序列化方法读取 PairingOutput
    PairingOutput::<Bls12_381>::deserialize_with_mode(cursor, Compress::No, Validate::Yes)
}
fn print_g1_as_bytes(g1_projective: G1Projective) -> Result<(), SerializationError> {
    // 将 G1Projective 转换为 G1Affine（仿射坐标）
    let g1_affine = g1_projective.into_affine();

    // 创建一个缓冲区来存储序列化后的字节
    let mut buffer = Vec::new();
    let mut writer = Cursor::new(&mut buffer);

    // 序列化 G1Affine 元素为字节
    G1Affine::serialize_with_mode(&g1_affine, &mut writer, Compress::No)?;

    // 打印字节
    println!("G1 element serialized as bytes: {:?}", buffer);

    Ok(())
}
fn print_g2_as_bytes(g2_projective: G2Projective) -> Result<(), SerializationError> {
    // 将 G2Projective 转换为 G2Affine（仿射坐标）
    let g2_affine = g2_projective.into_affine();

    // 创建一个缓冲区来存储序列化后的字节
    let mut buffer = Vec::new();
    let mut writer = Cursor::new(&mut buffer);

    // 使用提供的 serialize_with_mode 函数序列化 G2Affine 元素为字节
    G2Affine::serialize_with_mode(&g2_affine, &mut writer, Compress::No)?;

    // 打印字节
    println!("G2 element serialized as bytes: {:?}", buffer);

    Ok(())
}
fn print_pairing_output_as_bytes(pairing_output: PairingOutput<Bls12_381>) -> Result<(), SerializationError> {
    // 创建一个缓冲区来存储序列化后的字节
    let mut buffer = Vec::new();
    let mut writer = Cursor::new(&mut buffer);

    // 使用序列化函数将 PairingOutput 序列化为字节
    pairing_output.serialize_with_mode(&mut writer, Compress::No)?;

    // 打印字节
    println!("PairingOutput serialized as bytes: {:?}", buffer);

    Ok(())
}


fn create_proof(){
    type Polymath = sigma0_polymath::Polymath<Bls12_381, MerlinFieldTranscript<Fr>>;
    //初始化输入
    let sigma_aff:G1Affine = G1Projective::generator().into_affine();
    let g2_aff:G2Affine = G2Projective::generator().into_affine();
    let sigma: G1Projective = sigma_aff.into_group();
    let g2: G2Projective = g2_aff.into_group();
    //let _ = print_pairing_output_as_bytes(tmp_left);
    let mut rng = thread_rng();
    let scalar = ark_bls12_381::Fr::rand(&mut rng);
    let sigma_scar: G1Projective= sigma_aff.mul(scalar);
    let g2_scar:G2Projective= g2_aff.mul(scalar);
    let tmp_left:PairingOutput<Bls12_381> = Bls12_381::pairing(sigma, g2_scar);
    println!("tmp_left_out:{:?}",tmp_left);
    let tmp_right:PairingOutput<Bls12_381> = Bls12_381::pairing(sigma_scar, g2);
    println!("tmp_right_out:{:?}",tmp_right);

    let b: Fp<MontBackend<ark_bls12_381::FrConfig, 4>, 4> = Fp::ONE;

    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());


    println!("Creating parameters...");
    let start = Instant::now();
    //println!("sigma:{:?}",sigma);
    //println!("g2:{g2}");
    //println!("tmp:{tmp_left}");
    let (pk, vk) = {
        let c: RaichooSigCircuit<Fp<MontBackend<ark_bls12_381::FrConfig, 4>, 4>> = RaichooSigCircuit::<Fr>{sigma:G1Projective::generator(),g2: G2Projective::generator(),tmp_left:PairingOutput::ZERO,sigma_scar: sigma_scar,g2_scar:g2_scar,tmp_right:PairingOutput::ZERO, _marker: PhantomData};

        Polymath::setup(c, &mut rng).unwrap()
    };
    let pvk = Polymath::process_vk(&vk).unwrap();
    let setup_time = start.elapsed();
    let setup_time =
        setup_time.subsec_nanos() as f64 / 1_000_000_000f64 + (setup_time.as_secs() as f64);
    println!("Setup time: {:?} seconds", setup_time);
    // 构造电路
    const SAMPLES: u32 = 1;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    // let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        
        ///let prod= hash_right;
        let circuit = RaichooSigCircuit ::<Fr>{
            sigma:sigma,
            g2:g2,
            tmp_left:tmp_left,
            sigma_scar: sigma_scar,
            g2_scar: g2_scar,
            tmp_right:tmp_right,
            _marker: PhantomData, 
        };

        println!("Create proofs...");
        // 创建证明
        let start = Instant::now();
        let proof: sigma0_polymath::Proof<ark_ec::bls12::Bls12<ark_bls12_381::Config>> = Polymath::prove(&pk, circuit, &mut rng).unwrap();
        let proof_size = mem::size_of_val(&proof);
        println!("The size of the proof is {} bytes", proof_size);
        let provetime = start.elapsed();
        let provetime = provetime.subsec_nanos() as f64 / 1_000_000_000f64 + (provetime.as_secs() as f64);
        println!("Prove generate time:{:?} seconds",provetime);
        total_proving += start.elapsed();

        let start = Instant::now();
        println!("Verify proofs...");
        assert!(Polymath::verify(&pvk, &[b], &proof).unwrap());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg =
        proving_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (proving_avg.as_secs() as f64);


    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg =
        verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64 + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}
fn generate_g_elements() -> (Vec<G1Projective>, Vec<G2Projective>){
    let mut rng = thread_rng();

    // 生成一个包含 54 个 G1Projective 元素的 Vec
    let g1_elements: Vec<G1Projective> = (0..54)
        .map(|_| G1Projective::rand(&mut rng)) // 随机生成 G1Projective 元素
        .collect();

    // 打印生成的 G1 元素
    for (i, element) in g1_elements.iter().enumerate() {
        //println!("G1 Element {}: {:?}", i, element);
    }
    let g2_elements: Vec<G2Projective> = (0..54)
        .map(|_| G2Projective::rand(&mut rng)) // 随机生成 G2Projective 元素
        .collect();

    // 打印生成的 G1 元素
    for (i, element) in g2_elements.iter().enumerate() {
        //println!("G2 Element {}: {:?}", i, element);
    }
    (g1_elements, g2_elements)
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mimc() {
        create_proof();
        //generate_g_elements();
        // 你可以使用 assert 来验证结果
        //assert_eq!(2 + 2, 4); // 示例测试断言
    }
}