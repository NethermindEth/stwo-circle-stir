#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unused_mut)]

use super::backend::{BackendForChannel, Column};
use super::channel::MerkleChannel;
use super::circle::{CirclePointIndex, Coset};
use super::circle_fft::{evaluate, prove_low_degree, verify_low_degree_proof, CircleStirProof};
use super::poly::circle::{CanonicCoset, SecureCirclePoly};
use super::vcs::ops::MerkleHasher;

pub const LOG_STOPPING_DEGREE: u32 = 1;
pub const LOG_FOLDING_PARAM: u32 = 2;

pub struct CircleStirParams {
    pub coset: Coset,
    pub maxdeg_plus_1: usize,
    pub eval_sizes: Vec<usize>,
    pub folding_params: Vec<usize>,
    pub eval_offsets: Vec<CirclePointIndex>,
    pub repetition_params: Vec<usize>,
    pub ood_rep: u32,
}

pub struct CircleStirSecureFieldProof<H: MerkleHasher> {
    pub proofs: Vec<CircleStirProof<H>>,
    pub log_ds: Vec<u32>,
}

pub fn prove_circle_stir_secure_poly<B: BackendForChannel<MC>, MC: MerkleChannel>(
    secure_circle_poly: SecureCirclePoly<B>,
) -> CircleStirSecureFieldProof<MC::H> {
    let mut proofs = vec![];
    let mut log_ds = vec![];

    for poly in secure_circle_poly.0 {
        let log_d = poly.log_size() - 1;
        let params = generate_proving_params(log_d, LOG_STOPPING_DEGREE, LOG_FOLDING_PARAM);
        let evaluate = evaluate(poly, &params.coset, CirclePointIndex(1));
        let prover_channel = &mut MC::C::default();

        let proof = prove_low_degree::<B, MC>(
            prover_channel,
            &params.coset,
            &params.eval_sizes,
            params.maxdeg_plus_1,
            &params.repetition_params,
            &params.folding_params,
            &evaluate.values.to_cpu(),
            &params.eval_offsets,
        )
        .unwrap();

        proofs.push(proof);
        log_ds.push(log_d);
    }

    CircleStirSecureFieldProof { proofs, log_ds }
}

pub fn verify_circle_stir_secure_poly<B: BackendForChannel<MC>, MC: MerkleChannel>(
    proof: CircleStirSecureFieldProof<MC::H>,
) -> bool {
    let proofs = proof.proofs;
    let log_ds = proof.log_ds;
    let mut results = vec![];

    for (proof, &log_d) in proofs.iter().zip(log_ds.iter()) {
        let verify_channel = &mut MC::C::default();
        let params = generate_proving_params(log_d, LOG_STOPPING_DEGREE, LOG_FOLDING_PARAM);
        let verify_res = verify_low_degree_proof::<B, MC>(
            verify_channel,
            proof,
            &params.coset,
            &params.eval_sizes,
            &params.repetition_params,
            &params.folding_params,
            &params.eval_offsets,
            log_d as usize,
        );
        results.push(verify_res);
    }

    results.iter().all(|x| x.is_ok())
}

pub fn generate_proving_params(
    log_d: u32,
    log_stopping_degree: u32,
    log_folding_param: u32,
) -> CircleStirParams {
    let coset = CanonicCoset::new(log_d + 2).coset;
    let init_offset: CirclePointIndex = CirclePointIndex(1);

    let m = ((log_d - log_stopping_degree) as f64 / log_folding_param as f64).ceil() as usize - 1;

    let size_l = coset.size();

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
    use num_traits::Zero;

    use super::generate_proving_params;
    use crate::core::backend::{Column, CpuBackend};
    use crate::core::channel::Blake2sChannel;
    use crate::core::circle::{CirclePoint, CirclePointIndex};
    use crate::core::circle_fft::{
        calculate_g_hat, calculate_rs, calculate_rs_and_g_rs, calculate_xs, calculate_xs2s,
        evaluate, fold_val, get_betas, interpolate, prove_low_degree, shift_g_hat,
        verify_low_degree_proof,
    };
    use crate::core::fields::m31::BaseField;
    use crate::core::fields::qm31::{SecureField, QM31};
    use crate::core::fields::{CircPolyInterpolation, Field, FieldCircPolyOps};
    use crate::core::poly::circle::CirclePoly;
    use crate::core::vcs::blake2_merkle::Blake2sMerkleChannel;

    #[test]
    fn test_prove_and_verify() {
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

        let verify_channel = &mut Blake2sChannel::default();
        let verify_res = verify_low_degree_proof::<CpuBackend, Blake2sMerkleChannel>(
            verify_channel,
            &proof_res,
            &params.coset,
            &params.eval_sizes,
            &params.repetition_params,
            &params.folding_params,
            &params.eval_offsets,
            log_d as usize,
        );
        assert!(verify_res.is_ok());
    }

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

        let eval_offsets = params.eval_offsets.clone();
        let eval_offsets_points = eval_offsets
            .iter()
            .map(|x| x.to_point())
            .collect::<Vec<_>>();
        let eval_sizes = params.eval_sizes.clone();
        let folding_params = params.folding_params.clone();
        let repetition_params = params.repetition_params.clone();
        let values = evaluate.values.clone();
        let mut coset = params.coset.clone();
        let ood_rep = 1;

        let mut xs = calculate_xs(&coset, eval_offsets[0]);
        let xs_points = xs.iter().map(|x| x.to_point()).collect::<Vec<_>>();

        if values.len() != xs.len() && xs.len() / 2 != eval_sizes[0] {
            assert!(false);
        }

        let mut vals = values.to_owned();

        let mut r_fold = CirclePoint {
            x: BaseField::from(1377508080),
            y: BaseField::from(2035645549),
        };
        let mut g_hat = vec![];

        let mut folded_len = 0;

        for i in 1..folding_params.len() + 1 {
            // # fold using r-fold
            if eval_sizes[i - 1] % folding_params[i - 1] != 0 {
                assert!(false);
            }

            folded_len = eval_sizes[i - 1] / folding_params[i - 1];
            let mut coset2 = coset.repeated_double(folded_len.ilog2());

            let xs2s = calculate_xs2s(coset2, folding_params[i - 1]);

            if i == 2 {
                // (1300800228, 574193615)
                r_fold = CirclePoint {
                    x: BaseField::from(1300800228),
                    y: BaseField::from(574193615),
                };
            }
            g_hat = calculate_g_hat(
                folded_len,
                folding_params[i - 1],
                eval_sizes[i - 1],
                r_fold,
                &vals,
                &xs2s,
                &xs,
            );

            if i == folding_params.len() {
                break;
            }
            if eval_sizes[i] % folded_len != 0 {
                assert!(false);
            }
            if eval_sizes[i - 1] % eval_sizes[i] != 0 {
                assert!(false);
            }

            let expand_factor = eval_sizes[i] / folded_len;
            let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];
            coset = coset.repeated_double(eval_size_scale.ilog2());
            coset2 = coset.repeated_double(expand_factor.ilog2());
            let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

            let g_hat_shift = shift_g_hat::<CpuBackend, Blake2sMerkleChannel>(
                &g_hat,
                coset,
                expand_factor,
                p_offset,
                eval_offsets[i],
            );

            xs = calculate_xs(&coset, eval_offsets[i]);
            let xs_points = xs.iter().map(|x| x.to_point()).collect::<Vec<_>>();

            // [(((2074834727, 1132982331), (1432421146, 1584772322)), ((913587039, 1052462600),
            // (1132107682, 2015946599)))]
            let r_outs: Vec<CirclePoint<SecureField>> = vec![CirclePoint {
                x: QM31::from_m31(
                    BaseField::from(2074834727),
                    BaseField::from(1132982331),
                    BaseField::from(1432421146),
                    BaseField::from(1584772322),
                ),
                y: QM31::from_m31(
                    BaseField::from(913587039),
                    BaseField::from(1052462600),
                    BaseField::from(1132107682),
                    BaseField::from(2015946599),
                ),
            }];

            let betas =
                get_betas::<CpuBackend, Blake2sMerkleChannel>(&coset2, p_offset, &g_hat, &r_outs);

            // (1300800228, 574193615)
            let r_fold = CirclePoint {
                x: BaseField::from(1300800228),
                y: BaseField::from(574193615),
            };

            // (1304604544, 1743647705)
            let r_comb = CirclePoint {
                x: BaseField::from(1304604544),
                y: BaseField::from(1743647705),
            };

            let t_vals = vec![21, 29, 30, 23];
            let t_shifts = vec![10, 14, 15, 11];
            let t_conj = vec![1, 1, 0, 1];

            if repetition_params[i - 1] % 2 != 0 {
                assert!(false);
            }

            let (rs, g_rs) = calculate_rs_and_g_rs(
                &r_outs, &betas, &t_shifts, &t_conj, &coset2, p_offset, &g_hat, folded_len,
            );

            vals = fold_val(
                &rs,
                &g_rs,
                &xs,
                eval_sizes[i],
                r_comb,
                &g_hat_shift.values.to_cpu(),
                ood_rep,
            );
        }

        let final_folding_param = folding_params[folding_params.len() - 1];
        let to_shift = eval_offsets[eval_offsets.len() - 1] * final_folding_param;
        let g_pol = interpolate::<CpuBackend, Blake2sMerkleChannel>(
            &coset.repeated_double((final_folding_param as u32).ilog2()),
            to_shift,
            &g_hat,
        );

        let numer = params.maxdeg_plus_1;
        let denom: usize = folding_params.iter().product();
        let final_deg = numer / denom;

        let g_pol_coeffs: Vec<BaseField> = g_pol.coeffs.to_cpu();
        let (g_pol_final, g_pol_zeroes) = g_pol_coeffs.split_at(2 * final_deg + 1);

        let is_zero = g_pol_zeroes.iter().all(|x| *x == BaseField::zero());
        if !is_zero {
            assert!(false);
        }

        let g_pol_final_secure: Vec<QM31> = g_pol_final
            .iter()
            .map(|g| SecureField::from_single_m31(*g))
            .collect();

        println!("g_pol_final_secure: {:?}", g_pol_final_secure);
    }

    #[test]
    fn test_verify() {
        let log_d = 4;
        let log_stopping_degree = 1;
        let log_folding_param = 2;
        let params = generate_proving_params(log_d, log_stopping_degree, log_folding_param);

        let mut coset = params.coset.clone();
        let folding_params = params.folding_params.clone();
        let eval_sizes = params.eval_sizes.clone();
        let eval_offsets = params.eval_offsets.clone();
        let repetition_params = params.repetition_params.clone();
        let ood_rep = params.ood_rep as usize;
        let maxdeg_plus_1 = params.maxdeg_plus_1;

        let mut r_fold = CirclePoint::<BaseField> {
            x: BaseField::from(1377508080),
            y: BaseField::from(2035645549),
        };

        let mut r_comb = CirclePoint::<BaseField>::zero();
        let mut rs = vec![];
        let mut zpol = [vec![], vec![]];
        let mut g_rs = vec![];
        let mut pol = [vec![], vec![]];

        for i in 1..folding_params.len() {
            let folded_len = eval_sizes[i - 1] / folding_params[i - 1];
            let expand_factor = eval_sizes[i] / folded_len;
            let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];

            let coset_new = coset.repeated_double(eval_size_scale.ilog2());
            let coset2 = coset_new.repeated_double(expand_factor.ilog2());
            let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

            // [(((2074834727, 1132982331), (1432421146, 1584772322)), ((913587039, 1052462600),
            // (1132107682, 2015946599)))] let r_outs =
            // vec![CirclePointIndex(1).to_secure_field_point()];
            let r_outs = vec![CirclePoint {
                x: QM31::from_m31(
                    BaseField::from(2074834727),
                    BaseField::from(1132982331),
                    BaseField::from(1432421146),
                    BaseField::from(1584772322),
                ),
                y: QM31::from_m31(
                    BaseField::from(913587039),
                    BaseField::from(1052462600),
                    BaseField::from(1132107682),
                    BaseField::from(2015946599),
                ),
            }];

            let betas = vec![QM31::from_m31(
                BaseField::from(1961442338),
                BaseField::from(457087730),
                BaseField::from(1627736045),
                BaseField::from(1443152547),
            )];

            let r_fold_new = CirclePoint {
                x: BaseField::from(1300800228),
                y: BaseField::from(574193615),
            };
            let r_comb_new = CirclePoint {
                x: BaseField::from(1304604544),
                y: BaseField::from(1743647705),
            };

            let t_vals: Vec<u32> = vec![21, 29, 30, 23];
            let t_shifts: Vec<u32> = vec![10, 14, 15, 11];
            let t_conj: Vec<u32> = vec![1, 1, 0, 1];

            let rs_new = calculate_rs(&r_outs, &t_shifts, &t_conj, &coset2, p_offset);

            let temp_coset2 = coset.repeated_double(folded_len.ilog2());
            let xs2s = calculate_xs2s(temp_coset2, folding_params[i - 1]);
            let xs2s_points_0 = xs2s[0].iter().map(|x| x.to_point()).collect::<Vec<_>>();
            let xs2s_points_1 = xs2s[1].iter().map(|x| x.to_point()).collect::<Vec<_>>();

            // let mut vals = (0..16).map(|i| BaseField::from(i)).collect::<Vec<_>>();
            let mut vals = vec![
                BaseField::from(315540234),
                BaseField::from(371471913),
                BaseField::from(223204907),
                BaseField::from(645367083),
                BaseField::from(140382779),
                BaseField::from(2086642536),
                BaseField::from(711192913),
                BaseField::from(1621508428),
                BaseField::from(1839425160),
                BaseField::from(1863195319),
                BaseField::from(1167091139),
                BaseField::from(1372741300),
                BaseField::from(1805249102),
                BaseField::from(455098104),
                BaseField::from(27280341),
                BaseField::from(764480038),
            ];

            let mut g_hat = vec![];

            for (k, val) in (0..repetition_params[i - 1]).zip(vals.chunks(folding_params[i - 1])) {
                let intr = coset.step_size * (t_shifts[k] as usize);
                let intr_point = intr.to_point();
                let mut x0 = intr + eval_offsets[i - 1];
                if t_conj[k] % 2 != 0 {
                    x0 = x0.conj();
                }

                let x0_point = x0.to_point();

                let mut v_s = vec![];
                if i != 1 {
                    for (j, v) in val.iter().enumerate() {
                        let ind = t_shifts[k] as usize + j * folded_len;
                        let mut x: CirclePointIndex = coset.step_size * ind + eval_offsets[i - 1];
                        if t_conj[k] % 2 != 0 {
                            x = x.conj();
                        }

                        let d: QM31 = (*v - pol.eval_circ_poly_at(&x.to_point()))
                            / zpol.eval_circ_poly_at(&x.to_secure_field_point());

                        let m = d.0 .0 * ((x.to_point() + r_comb).x).geom_sum(rs.len());
                        v_s.push(m);
                    }
                } else {
                    v_s.append(&mut val.to_vec());
                }

                let lagrange_interp = xs2s[t_conj[k] as usize]
                    .iter()
                    .map(|x| x.to_point())
                    .collect::<Vec<_>>()
                    .circ_lagrange_interp(&v_s, true)
                    .unwrap();
                let x0_conj_point = x0.conj().to_point();
                let mult = r_fold + x0_conj_point;
                let eval_circ_poly_at = lagrange_interp.eval_circ_poly_at(&mult);
                g_hat.push(eval_circ_poly_at);
            }

            coset = coset_new;
            r_fold = r_fold_new;
            r_comb = r_comb_new;
            rs = rs_new;
            zpol = rs.circ_zpoly(None, true, Some(ood_rep));
            g_rs = betas
                .into_iter()
                .chain(g_hat.into_iter().map(|x| QM31::from_single_m31(x)))
                .collect();
            pol = rs.circ_lagrange_interp(&g_rs, false).unwrap();
        }

        let denom: usize = folding_params.iter().product();
        let final_deg = maxdeg_plus_1 / denom;

        if eval_sizes[eval_sizes.len() - 1] % folding_params[folding_params.len() - 1] != 0 {
            assert!(false);
        }
        let folded_len =
            eval_sizes[eval_sizes.len() - 1] / folding_params[folding_params.len() - 1];
        let coset2 = coset.repeated_double(folding_params[folding_params.len() - 1].ilog2());

        // override values

        // // [[1968990132, 1934878866, 300414560, 887535011, 2085955806], [9830192, 606435100,
        // // 1870620053, 1095259688]]
        // let pol = [
        //     vec![
        //         BaseField::from(1968990132),
        //         BaseField::from(1934878866),
        //         BaseField::from(300414560),
        //         BaseField::from(887535011),
        //         BaseField::from(2085955806),
        //     ],
        //     vec![
        //         BaseField::from(9830192),
        //         BaseField::from(606435100),
        //         BaseField::from(1870620053),
        //         BaseField::from(1095259688),
        //     ],
        // ];

        // // [[1608407134, 368761548, 371080277, 1221644124, 1105186116], [865278165, 698439612,
        // // 1950138262, 331766842]]
        // let zpol = [
        //     vec![
        //         QM31::from_single_m31(BaseField::from(1608407134)),
        //         QM31::from_single_m31(BaseField::from(368761548)),
        //         QM31::from_single_m31(BaseField::from(371080277)),
        //         QM31::from_single_m31(BaseField::from(1221644124)),
        //         QM31::from_single_m31(BaseField::from(1105186116)),
        //     ],
        //     vec![
        //         QM31::from_single_m31(BaseField::from(865278165)),
        //         QM31::from_single_m31(BaseField::from(698439612)),
        //         QM31::from_single_m31(BaseField::from(1950138262)),
        //         QM31::from_single_m31(BaseField::from(331766842)),
        //     ],
        // ];

        // (550310314093913240, 2418604250860003780)
        let r_comb = CirclePoint::<BaseField> {
            x: BaseField::from(1304604544),
            y: BaseField::from(1743647705),
        };

        // (1300800228, 574193615)
        let r_fold = CirclePoint::<BaseField> {
            x: BaseField::from(1300800228),
            y: BaseField::from(574193615),
        };

        let g_pol_final = vec![
            BaseField::from(688324166),
            BaseField::from(825768464),
            BaseField::from(1440309969),
        ];
        let g_pol_final_secure: Vec<QM31> = g_pol_final
            .iter()
            .map(|g| SecureField::from_single_m31(*g))
            .collect();

        let t_vals = vec![7, 14, 4, 1];
        let t_shifts = vec![3, 7, 2, 0];
        let t_conj = vec![1, 0, 0, 1];

        let coset3 = coset.repeated_double(folded_len.ilog2());
        let xs2s = calculate_xs2s(coset3, folding_params[folding_params.len() - 1]);

        let mut vals = vec![
            BaseField::from(486321191),
            BaseField::from(228684397),
            BaseField::from(2082673974),
            BaseField::from(710569464),
            BaseField::from(414168975),
            BaseField::from(885599309),
            BaseField::from(1009399098),
            BaseField::from(167499685),
            BaseField::from(1972915090),
            BaseField::from(1364122922),
            BaseField::from(737988605),
            BaseField::from(1727862060),
            BaseField::from(826253630),
            BaseField::from(460282993),
            BaseField::from(1315962948),
            BaseField::from(1623363144),
        ];

        for (k, val) in (0..repetition_params[repetition_params.len() - 1])
            .zip(vals.chunks(folding_params[folding_params.len() - 1]))
        {
            let intr = coset.step_size * (t_shifts[k] as usize);
            let intr_point = intr.to_point();
            let eval_offset_point = eval_offsets[eval_offsets.len() - 1].to_point();
            let mut x0 = intr + eval_offsets[eval_offsets.len() - 1];
            let x0_point = x0.to_point();
            if t_conj[k] % 2 != 0 {
                x0 = x0.conj();
            }
            let x0_conj_point = x0.to_point();

            let mut v_s = vec![];
            for (j, v) in val.iter().enumerate() {
                let ind = t_shifts[k] as usize + j * folded_len;
                let mut x: CirclePointIndex =
                    coset.step_size * ind + eval_offsets[eval_offsets.len() - 1];
                if t_conj[k] % 2 != 0 {
                    x = x.conj();
                }
                let x_point = x.to_point();

                let d: QM31 = (*v - pol.eval_circ_poly_at(&x.to_point()))
                    / zpol.eval_circ_poly_at(&x.to_secure_field_point());

                let m = d.0 .0 * ((x.to_point() + r_comb).x).geom_sum(rs.len());
                v_s.push(m);
            }

            let lagrange_interp = xs2s[t_conj[k] as usize]
                .iter()
                .map(|x| x.to_point())
                .collect::<Vec<_>>()
                .circ_lagrange_interp(&v_s, true)
                .unwrap();
            let mult = r_fold + x0.conj().to_point();
            let lhs = lagrange_interp.eval_circ_poly_at(&mult);

            let mut offset = coset2.step_size * t_shifts[k] as usize
                + eval_offsets[eval_offsets.len() - 1] * folding_params[folding_params.len() - 1];
            let offset_point = offset.to_point();

            if t_conj[k] % 2 != 0 {
                offset = offset.conj();
            }
            let offset_point2 = offset.to_point();

            let mut coeffs: Vec<BaseField> = g_pol_final.iter().map(|x| *x).collect();
            if !coeffs.len().is_power_of_two() {
                let next_power_of_two = coeffs.len().next_power_of_two();
                coeffs.resize(next_power_of_two, BaseField::from(0));
            }

            let rhs = CirclePoly::<CpuBackend>::new(coeffs.iter().map(|x| *x).collect())
                .eval_at_point(offset.to_secure_field_point())
                .0
                 .0;

            if lhs != rhs {
                assert!(false);
            }
        }
    }

    // test are done by copy pasting the code and modifying the randomness
    // to refactor by using mock random functions
    #[test]
    fn test_verify2() {
        let log_d = 4;
        let log_stopping_degree = 1;
        let log_folding_param = 2;
        let params = generate_proving_params(log_d, log_stopping_degree, log_folding_param);

        let mut coset = params.coset.clone();
        let folding_params = params.folding_params.clone();
        let eval_sizes = params.eval_sizes.clone();
        let eval_offsets = params.eval_offsets.clone();
        let repetition_params = params.repetition_params.clone();
        let ood_rep = params.ood_rep as usize;
        let maxdeg_plus_1 = params.maxdeg_plus_1;

        let mut r_fold = CirclePoint::<BaseField> {
            x: BaseField::from(1377508080),
            y: BaseField::from(2035645549),
        };

        let mut r_comb = CirclePoint::<BaseField>::zero();
        let mut rs = vec![];
        let mut zpol = [vec![], vec![]];
        let mut g_rs = vec![];
        let mut pol = [vec![], vec![]];

        for i in 1..folding_params.len() {
            if eval_sizes[i - 1] % folding_params[i - 1] != 0 {
                assert!(false);
            }

            let folded_len = eval_sizes[i - 1] / folding_params[i - 1];
            if eval_sizes[i] % folded_len != 0 {
                assert!(false);
            }
            let expand_factor = eval_sizes[i] / folded_len;
            if eval_sizes[i - 1] % eval_sizes[i] != 0 {
                assert!(false);
            }
            let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];

            let coset_new = coset.repeated_double(eval_size_scale.ilog2());
            let coset2 = coset_new.repeated_double(expand_factor.ilog2());
            let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

            let r_outs = vec![CirclePoint {
                x: QM31::from_m31(
                    BaseField::from(2074834727),
                    BaseField::from(1132982331),
                    BaseField::from(1432421146),
                    BaseField::from(1584772322),
                ),
                y: QM31::from_m31(
                    BaseField::from(913587039),
                    BaseField::from(1052462600),
                    BaseField::from(1132107682),
                    BaseField::from(2015946599),
                ),
            }];

            let betas = vec![QM31::from_m31(
                BaseField::from(1961442338),
                BaseField::from(457087730),
                BaseField::from(1627736045),
                BaseField::from(1443152547),
            )];

            let r_fold_new = CirclePoint {
                x: BaseField::from(1300800228),
                y: BaseField::from(574193615),
            };
            let r_comb_new = CirclePoint {
                x: BaseField::from(1304604544),
                y: BaseField::from(1743647705),
            };

            let t_vals: Vec<u32> = vec![21, 29, 30, 23];
            let t_shifts: Vec<u32> = vec![10, 14, 15, 11];
            let t_conj: Vec<u32> = vec![1, 1, 0, 1];

            let rs_new = calculate_rs(&r_outs, &t_shifts, &t_conj, &coset2, p_offset);

            let temp_coset2 = coset.repeated_double(folded_len.ilog2());
            let xs2s = calculate_xs2s(temp_coset2, folding_params[i - 1]);

            let mut vals = vec![
                BaseField::from(315540234),
                BaseField::from(371471913),
                BaseField::from(223204907),
                BaseField::from(645367083),
                BaseField::from(140382779),
                BaseField::from(2086642536),
                BaseField::from(711192913),
                BaseField::from(1621508428),
                BaseField::from(1839425160),
                BaseField::from(1863195319),
                BaseField::from(1167091139),
                BaseField::from(1372741300),
                BaseField::from(1805249102),
                BaseField::from(455098104),
                BaseField::from(27280341),
                BaseField::from(764480038),
            ];

            let mut g_hat = vec![];

            for (k, val) in (0..repetition_params[i - 1]).zip(vals.chunks(folding_params[i - 1])) {
                let intr = coset.step_size * (t_shifts[k] as usize);
                let mut x0 = intr + eval_offsets[i - 1];
                if t_conj[k] % 2 != 0 {
                    x0 = x0.conj();
                }

                let mut v_s = vec![];
                if i != 1 {
                    for (j, v) in val.iter().enumerate() {
                        let ind = t_shifts[k] as usize + j * folded_len;
                        let mut x: CirclePointIndex = coset.step_size * ind + eval_offsets[i - 1];
                        if t_conj[k] % 2 != 0 {
                            x = x.conj();
                        }

                        let d: QM31 = (*v - pol.eval_circ_poly_at(&x.to_point()))
                            / zpol.eval_circ_poly_at(&x.to_secure_field_point());

                        let m = d.0 .0 * ((x.to_point() + r_comb).x).geom_sum(rs.len());
                        v_s.push(m);
                    }
                } else {
                    v_s.append(&mut val.to_vec());
                }

                let lagrange_interp = xs2s[t_conj[k] as usize]
                    .iter()
                    .map(|x| x.to_point())
                    .collect::<Vec<_>>()
                    .circ_lagrange_interp(&v_s, true)
                    .unwrap();
                let mult = r_fold + x0.conj().to_point();
                let eval_circ_poly_at = lagrange_interp.eval_circ_poly_at(&mult);
                g_hat.push(eval_circ_poly_at);
            }

            coset = coset_new;
            r_fold = r_fold_new;
            r_comb = r_comb_new;
            rs = rs_new;
            zpol = rs.circ_zpoly(None, true, Some(ood_rep));
            g_rs = betas
                .into_iter()
                .chain(g_hat.into_iter().map(|x| QM31::from_single_m31(x)))
                .collect();
            pol = rs.circ_lagrange_interp(&g_rs, false).unwrap();
        }

        // next section

        let denom: usize = folding_params.iter().product();
        let final_deg = maxdeg_plus_1 / denom;

        if eval_sizes[eval_sizes.len() - 1] % folding_params[folding_params.len() - 1] != 0 {
            assert!(false);
        }
        let folded_len =
            eval_sizes[eval_sizes.len() - 1] / folding_params[folding_params.len() - 1];
        let coset2 = coset.repeated_double(folding_params[folding_params.len() - 1].ilog2());

        let g_pol_final = vec![
            BaseField::from(688324166),
            BaseField::from(825768464),
            BaseField::from(1440309969),
        ];

        let t_vals = vec![7, 14, 4, 1];
        let t_shifts = vec![3, 7, 2, 0];
        let t_conj = vec![1, 0, 0, 1];

        let coset3 = coset.repeated_double(folded_len.ilog2());
        let xs2s = calculate_xs2s(coset3, folding_params[folding_params.len() - 1]);

        let mut vals = vec![
            BaseField::from(486321191),
            BaseField::from(228684397),
            BaseField::from(2082673974),
            BaseField::from(710569464),
            BaseField::from(414168975),
            BaseField::from(885599309),
            BaseField::from(1009399098),
            BaseField::from(167499685),
            BaseField::from(1972915090),
            BaseField::from(1364122922),
            BaseField::from(737988605),
            BaseField::from(1727862060),
            BaseField::from(826253630),
            BaseField::from(460282993),
            BaseField::from(1315962948),
            BaseField::from(1623363144),
        ];

        for (k, val) in (0..repetition_params[repetition_params.len() - 1])
            .zip(vals.chunks(folding_params[folding_params.len() - 1]))
        {
            let intr = coset.step_size * (t_shifts[k] as usize);
            let mut x0 = intr + eval_offsets[eval_offsets.len() - 1];
            if t_conj[k] % 2 != 0 {
                x0 = x0.conj();
            }

            let mut v_s = vec![];
            for (j, v) in val.iter().enumerate() {
                let ind = t_shifts[k] as usize + j * folded_len;
                let mut x: CirclePointIndex =
                    coset.step_size * ind + eval_offsets[eval_offsets.len() - 1];
                if t_conj[k] % 2 != 0 {
                    x = x.conj();
                }

                let d: QM31 = (*v - pol.eval_circ_poly_at(&x.to_point()))
                    / zpol.eval_circ_poly_at(&x.to_secure_field_point());

                let m = d.0 .0 * ((x.to_point() + r_comb).x).geom_sum(rs.len());
                v_s.push(m);
            }

            let lagrange_interp = xs2s[t_conj[k] as usize]
                .iter()
                .map(|x| x.to_point())
                .collect::<Vec<_>>()
                .circ_lagrange_interp(&v_s, true)
                .unwrap();
            let mult = r_fold + x0.conj().to_point();
            let lhs = lagrange_interp.eval_circ_poly_at(&mult);

            let mut offset = coset2.step_size * t_shifts[k] as usize
                + eval_offsets[eval_offsets.len() - 1] * folding_params[folding_params.len() - 1];

            if t_conj[k] % 2 != 0 {
                offset = offset.conj();
            }

            let mut coeffs: Vec<BaseField> = g_pol_final.iter().map(|x| *x).collect();
            if !coeffs.len().is_power_of_two() {
                let next_power_of_two = coeffs.len().next_power_of_two();
                coeffs.resize(next_power_of_two, BaseField::from(0));
            }
            let rhs = CirclePoly::<CpuBackend>::new(coeffs.iter().map(|x| *x).collect())
                .eval_at_point(offset.to_secure_field_point())
                .0
                 .0;

            if lhs != rhs {
                assert!(false);
            }
        }
    }
}
