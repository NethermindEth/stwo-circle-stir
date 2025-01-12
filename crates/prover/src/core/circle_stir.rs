#![allow(unused_variables)]
#![allow(unused_assignments)]

use super::circle::{CirclePointIndex, Coset};
use super::poly::circle::CanonicCoset;

pub struct CircleStirParams {
    pub coset: Coset,
    pub maxdeg_plus_1: usize,
    pub eval_sizes: Vec<usize>,
    pub folding_params: Vec<usize>,
    pub eval_offsets: Vec<CirclePointIndex>,
    pub repetition_params: Vec<usize>,
    pub ood_rep: u32,
}

pub fn generate_proving_params(
    log_d: u32,
    log_stopping_degree: u32,
    log_folding_param: u32,
    // security_param: usize,
    // proximity_param: usize,
) -> CircleStirParams {
    let coset = CanonicCoset::new(log_d + 2).coset;
    let init_offset: CirclePointIndex = CirclePointIndex(1);

    let m = ((log_d - log_stopping_degree) / log_folding_param) as usize;
    let size_l = coset.size();
    // assert!(0 < proximity_param <= 1);

    let mut eval_sizes = vec![size_l];
    let mut eval_offsets = vec![init_offset];
    let mut rt = coset.step_size;

    for i in 1..m + 1 {
        eval_sizes.push(eval_sizes[i as usize - 1] / 2);
        eval_offsets.push(rt + init_offset);
        rt = rt + rt;
    }

    CircleStirParams {
        coset,
        maxdeg_plus_1: 1 << log_d,
        folding_params: vec![1 << log_folding_param; m + 1],
        eval_offsets,
        eval_sizes,
        repetition_params: vec![4; m + 1],
        ood_rep: 1,
    }
}

#[cfg(test)]
mod tests {
    use super::generate_proving_params;
    use crate::core::backend::CpuBackend;
    use crate::core::channel::Blake2sChannel;
    use crate::core::circle::CirclePointIndex;
    use crate::core::circle_fft::{evaluate, prove_low_degree, verify_low_degree_proof};
    use crate::core::fields::m31::BaseField;
    use crate::core::poly::circle::CirclePoly;
    use crate::core::vcs::blake2_merkle::Blake2sMerkleChannel;

    #[test]
    fn test_prove() {
        let prover_channel = &mut Blake2sChannel::default();
        let log_d = 4;
        let log_stopping_degree = 1;
        let log_folding_param = 2;
        let params = generate_proving_params(log_d, log_stopping_degree, log_folding_param);

        let poly = (0..1 << (log_d + 1))
            .map(|i| BaseField::from(i))
            .collect::<Vec<_>>();
        let poly: CirclePoly<CpuBackend> = CirclePoly::<CpuBackend>::new(poly);
        let evaluate =
            evaluate::<CpuBackend, Blake2sMerkleChannel>(poly, &params.coset, CirclePointIndex(1));

        let proof_res = prove_low_degree::<CpuBackend, Blake2sMerkleChannel>(
            prover_channel,
            &params.coset,
            &params.eval_sizes,
            params.maxdeg_plus_1,
            &params.repetition_params,
            &params.folding_params,
            &evaluate.values,
            &params.eval_offsets,
        )
        .unwrap();

        // println!("proof_res: {:?}", proof_res);
        let verify_channel = &mut Blake2sChannel::default();
        let verify_res = verify_low_degree_proof::<CpuBackend, Blake2sMerkleChannel>(
            verify_channel,
            proof_res,
            &params.coset,
            &params.eval_sizes,
            &params.repetition_params,
            &params.folding_params,
            &params.eval_offsets,
            log_d as usize,
        );
    }
}
