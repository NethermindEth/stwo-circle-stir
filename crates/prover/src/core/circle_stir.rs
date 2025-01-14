#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unused_mut)]

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
    use crate::core::circle::{CirclePoint, CirclePointIndex};
    use crate::core::circle_fft::{
        calculate_rs, calculate_xs2s, circ_lagrange_interp, circ_zpoly, eval_circ_poly_at,
        evaluate, geom_sum, prove_low_degree, verify_low_degree_proof, Conj,
    };
    use crate::core::fields::m31::BaseField;
    use crate::core::fields::qm31::{SecureField, QM31};
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

        let mut r_fold = CirclePointIndex(1).to_point();
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

            let r_outs = vec![CirclePointIndex(1).to_secure_field_point()];
            let betas = vec![QM31::from_single_m31(BaseField::from(1))];

            let r_fold_new = CirclePointIndex(1).to_point();
            let r_comb_new = CirclePointIndex(1).to_point();
            let t_vals: Vec<u32> = vec![1, 2, 3, 4];
            let t_shifts: Vec<u32> = vec![1, 2, 3, 4];
            let t_conj: Vec<u32> = vec![1, 0, 1, 0];

            let rs_new = calculate_rs(&r_outs, &t_shifts, &t_conj, &coset2, p_offset);

            let temp_coset2 = coset.repeated_double(folded_len.ilog2());
            let xs2s = calculate_xs2s(temp_coset2, folding_params[i - 1]);
            let xs2s_points_0 = xs2s[0].iter().map(|x| x.to_point()).collect::<Vec<_>>();
            let xs2s_points_1 = xs2s[1].iter().map(|x| x.to_point()).collect::<Vec<_>>();

            let mut vals = (0..16).map(|i| BaseField::from(i)).collect::<Vec<_>>();

            let mut g_hat = vec![];

            for (k, val) in (0..repetition_params[i - 1]).zip(vals.chunks(folding_params[i - 1])) {
                let intr = coset.step_size * (t_shifts[k] as usize);
                let intr_point = intr.to_point();
                let mut x0 = intr + eval_offsets[i - 1];
                if k % 2 == 0 {
                    x0 = x0.conj();
                }

                let x0_point = x0.to_point();

                let mut v_s = vec![];
                if i != 1 {
                    for (j, v) in val.iter().enumerate() {
                        let ind = t_shifts[k] as usize + j * folded_len;
                        let mut x: CirclePointIndex = coset.step_size * ind + eval_offsets[i - 1];
                        if k % 2 == 0 {
                            x = x.conj();
                        }

                        let val = vals[j];
                        let d = (val - eval_circ_poly_at(&pol, &x.to_point()))
                            / eval_circ_poly_at(&zpol, &x.to_secure_field_point());

                        let m = d.0 .0 * geom_sum((x.to_point() + r_comb).x, rs.len());
                        v_s.push(m);
                    }
                } else {
                    v_s.append(&mut val.to_vec());
                }

                let lagrange_interp = circ_lagrange_interp(
                    &xs2s[t_conj[k] as usize]
                        .iter()
                        .map(|x| x.to_point())
                        .collect(),
                    &v_s,
                    true,
                )
                .unwrap();
                let x0_conj_point = x0.conj().to_point();
                let mult = r_fold + x0_conj_point;
                let eval_circ_poly_at = eval_circ_poly_at(&lagrange_interp, &mult);
                g_hat.push(eval_circ_poly_at);
            }

            coset = coset_new;
            r_fold = r_fold_new;
            r_comb = r_comb_new;
            rs = rs_new;
            zpol = circ_zpoly(&rs, None, true, Some(ood_rep));
            g_rs = betas
                .into_iter()
                .chain(g_hat.into_iter().map(|x| QM31::from_single_m31(x)))
                .collect();
            pol = circ_lagrange_interp(&rs, &g_rs, false).unwrap();
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

        // [[1968990132, 1934878866, 300414560, 887535011, 2085955806], [9830192, 606435100,
        // 1870620053, 1095259688]]
        let pol = [
            vec![
                BaseField::from(1968990132),
                BaseField::from(1934878866),
                BaseField::from(300414560),
                BaseField::from(887535011),
                BaseField::from(2085955806),
            ],
            vec![
                BaseField::from(9830192),
                BaseField::from(606435100),
                BaseField::from(1870620053),
                BaseField::from(1095259688),
            ],
        ];

        // [[1608407134, 368761548, 371080277, 1221644124, 1105186116], [865278165, 698439612,
        // 1950138262, 331766842]]
        let zpol = [
            vec![
                QM31::from_single_m31(BaseField::from(1608407134)),
                QM31::from_single_m31(BaseField::from(368761548)),
                QM31::from_single_m31(BaseField::from(371080277)),
                QM31::from_single_m31(BaseField::from(1221644124)),
                QM31::from_single_m31(BaseField::from(1105186116)),
            ],
            vec![
                QM31::from_single_m31(BaseField::from(865278165)),
                QM31::from_single_m31(BaseField::from(698439612)),
                QM31::from_single_m31(BaseField::from(1950138262)),
                QM31::from_single_m31(BaseField::from(331766842)),
            ],
        ];

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
            if k % 2 == 0 {
                x0 = x0.conj();
            }
            let x0_point = x0.to_point();

            let mut v_s = vec![];
            for (j, v) in val.iter().enumerate() {
                let ind = t_shifts[k] as usize + j * folded_len;
                let mut x: CirclePointIndex =
                    coset.step_size * ind + eval_offsets[eval_offsets.len() - 1];
                if k % 2 == 0 {
                    x = x.conj();
                }
                let x_point = x.to_point();

                let val = vals[j];
                let d = (val - eval_circ_poly_at(&pol, &x.to_point()))
                    / eval_circ_poly_at(&zpol, &x.to_secure_field_point());

                let m = d.0 .0 * geom_sum((x.to_point() + r_comb).x, rs.len());
                v_s.push(m);
            }

            let lagrange_interp = circ_lagrange_interp(
                &xs2s[t_conj[k] as usize]
                    .iter()
                    .map(|x| x.to_point())
                    .collect(),
                &v_s,
                true,
            )
            .unwrap();
            let mult = r_fold + x0.conj().to_point();
            let lhs = eval_circ_poly_at(&lagrange_interp, &mult);

            let mut offset = coset2.step_size * t_shifts[k] as usize
                + eval_offsets[eval_offsets.len() - 1] * folding_params[folding_params.len() - 1];
            let offset_point = offset.to_point();

            if k % 2 == 0 {
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
}
