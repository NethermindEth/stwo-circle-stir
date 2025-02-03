#![allow(unused_variables)]
#![allow(unused_assignments)]

use std::collections::HashSet;
use std::vec;

use num_traits::Zero;
use serde::{Deserialize, Serialize};

use super::backend::{BackendForChannel, Column};
use super::channel::{Channel, MerkleChannel};
use super::circle::{CirclePoint, CirclePointIndex, Coset, M31_CIRCLE_GEN};
use super::fields::m31::{BaseField, M31, P};
use super::fields::qm31::{SecureField, QM31};
use super::fields::{CircPolyInterpolation, Field, FieldCircPolyOps};
use super::poly::circle::{CircleDomain, CircleEvaluation, CirclePoly};
use super::poly::NaturalOrder;
use super::simple_merkle::{verify_many_proof, MerkleProof, SimpleMerkleTree};
use super::vcs::ops::MerkleHasher;

pub fn interpolate<B: BackendForChannel<MC>, MC: MerkleChannel>(
    coset: &Coset,
    to_shift: CirclePointIndex,
    eval: &Vec<BaseField>,
) -> CirclePoly<B> {
    let shift_size = coset.shift(-to_shift).conjugate().initial_index;
    let domain = CircleDomain::new(coset.shift(shift_size));
    let evaluation = CircleEvaluation::<B, BaseField, NaturalOrder>::new(
        domain,
        eval.iter().map(|x| *x).collect(),
    );
    let poly = evaluation.clone().bit_reverse().interpolate();

    poly
}

pub fn evaluate<B: BackendForChannel<MC>, MC: MerkleChannel>(
    poly: CirclePoly<B>,
    coset: &Coset,
    offset: CirclePointIndex,
) -> CircleEvaluation<B, M31, NaturalOrder> {
    let to_shift = coset.shift(-offset).conjugate().initial_index;
    let domain = CircleDomain::new(coset.shift(to_shift));
    let evals = poly.evaluate(domain).bit_reverse();

    evals
}

pub fn calculate_g_hat(
    folded_len: usize,
    folding_param: usize,
    eval_size: usize,
    r_fold: CirclePoint<BaseField>,
    vals: &Vec<BaseField>,
    xs2s: &[Vec<CirclePointIndex>; 2],
    xs: &Vec<CirclePointIndex>,
) -> Vec<BaseField> {
    let mut x_polys: Vec<[Vec<BaseField>; 2]> = vec![];

    let mut xs2s_points: [Vec<CirclePoint<M31>>; 2] = [vec![], vec![]];
    xs2s_points[0] = xs2s[0].iter().map(|x| x.to_point()).collect();
    xs2s_points[1] = xs2s[1].iter().map(|x| x.to_point()).collect();

    let xs_points: Vec<CirclePoint<M31>> = xs.iter().map(|x| x.to_point()).collect();

    for l in 0..=1 {
        for k in 0..folded_len {
            let interp_vals: Vec<BaseField> = (0..folding_param)
                .map(|j| vals[k + folded_len * j + eval_size * l])
                .collect();
            // TODO: proper error handling instead of using 'unwrap'
            let inpl = xs2s[l]
                .iter()
                .map(|x| x.to_point())
                .collect::<Vec<_>>()
                .circ_lagrange_interp(&interp_vals, true)
                .unwrap();

            x_polys.push(inpl);
        }
    }

    let mut g_hat = vec![];
    for l in 0..=1 {
        for k in 0..folded_len {
            let polys = &x_polys[k + folded_len * l];
            let point = r_fold.mul_circle_point(xs[k + eval_size * l].to_point().conjugate());

            let eval = polys.eval_circ_poly_at(&point);
            g_hat.push(eval);
        }
    }

    g_hat
}

pub fn shift_g_hat<B: BackendForChannel<MC>, MC: MerkleChannel>(
    g_hat: &Vec<BaseField>,
    coset: Coset,
    expand_factor: usize,
    p_offset: CirclePointIndex,
    eval_offset: CirclePointIndex,
) -> CircleEvaluation<B, BaseField, NaturalOrder> {
    let interpolate_coset = coset.repeated_double(expand_factor.ilog2());
    let poly = interpolate::<B, MC>(&interpolate_coset, p_offset, g_hat);
    let g_hat_shift = evaluate::<B, MC>(poly, &coset, eval_offset);

    g_hat_shift
}

fn generate_rnd_t_values<MC: MerkleChannel>(
    channel: &mut MC::C,
    folded_len: usize,
    repetition_param: usize,
) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let mut t_vals_set = HashSet::<u32>::new();
    while t_vals_set.len() < repetition_param {
        let t_vals_bytes = channel.draw_random_bytes();
        let t_vals_bytes = [
            t_vals_bytes[0],
            t_vals_bytes[1],
            t_vals_bytes[2],
            t_vals_bytes[3],
        ];
        let t_val = u32::from_be_bytes(t_vals_bytes) % ((2 * folded_len) as u32);
        t_vals_set.insert(t_val);
    }

    let mut t_vals: Vec<u32> = t_vals_set.iter().cloned().collect();
    t_vals.sort();
    let t_shifts: Vec<u32> = t_vals.iter().map(|&t| t / 2).collect();
    let t_conj: Vec<u32> = t_vals.iter().map(|&t| t % 2).collect();

    (t_vals, t_shifts, t_conj)
}

fn generate_rnd_r_t_values<MC: MerkleChannel>(
    channel: &mut MC::C,
    folded_len: usize,
    repetition_param: usize,
) -> (
    CirclePoint<M31>,
    CirclePoint<M31>,
    Vec<u32>,
    Vec<u32>,
    Vec<u32>,
) {
    let rnds = channel.draw_felts(2);
    let r_fold = M31_CIRCLE_GEN.mul(rnds[0].0 .0 .0.into());
    let r_comb = M31_CIRCLE_GEN.mul(rnds[1].0 .0 .0.into());

    // mix again to get randomness of the next value
    channel.mix_felts(&rnds);
    let (t_vals, t_shifts, t_conj) =
        generate_rnd_t_values::<MC>(channel, folded_len, repetition_param);

    (r_fold, r_comb, t_vals, t_shifts, t_conj)
}

pub fn get_betas<B: BackendForChannel<MC>, MC: MerkleChannel>(
    coset: &Coset,
    p_offset: CirclePointIndex,
    g_hat: &Vec<BaseField>,
    r_outs: &Vec<CirclePoint<SecureField>>,
) -> Vec<SecureField> {
    let poly = interpolate::<B, MC>(coset, p_offset, g_hat);

    // TODO: to check correctness of this betas result
    let betas: Vec<SecureField> = r_outs
        .iter()
        .map(|o| poly.eval_at_point((*o).into()))
        .collect();

    betas
}

pub fn calculate_rs_and_g_rs(
    r_outs: &Vec<CirclePoint<SecureField>>,
    betas: &Vec<SecureField>,
    t_shifts: &Vec<u32>,
    t_conj: &Vec<u32>,
    coset: &Coset,
    p_offset: CirclePointIndex,
    g_hat: &Vec<BaseField>,
    folded_len: usize,
) -> (Vec<CirclePoint<SecureField>>, Vec<SecureField>) {
    let rs = calculate_rs(r_outs, t_shifts, t_conj, coset, p_offset);
    let g_rs = calculate_g_rs(betas, t_shifts, t_conj, g_hat, folded_len);

    (rs, g_rs)
}

pub fn calculate_rs(
    r_outs: &Vec<CirclePoint<SecureField>>,
    t_shifts: &Vec<u32>,
    t_conj: &Vec<u32>,
    coset: &Coset,
    p_offset: CirclePointIndex,
) -> Vec<CirclePoint<SecureField>> {
    let mut rs = r_outs.to_vec();

    for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
        let mut intr = p_offset + (coset.step_size * (*t as usize));
        let intr_point = intr.to_secure_field_point();

        if k % 2 != 0 {
            intr = intr.conj();
        }
        rs.push(intr.to_secure_field_point());
    }

    rs
}

fn calculate_g_rs(
    betas: &Vec<SecureField>,
    t_shifts: &Vec<u32>,
    t_conj: &Vec<u32>,
    g_hat: &Vec<BaseField>,
    folded_len: usize,
) -> Vec<SecureField> {
    let mut g_rs = betas.to_vec();

    for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
        let index = (*t as usize) + (*k as usize) * folded_len;
        let g_value = g_hat[index];
        g_rs.push(SecureField::from_single_m31(g_value))
    }

    g_rs
}

pub fn fold_val(
    rs: &Vec<CirclePoint<SecureField>>,
    g_rs: &Vec<SecureField>,
    xs: &Vec<CirclePointIndex>,
    eval_size: usize,
    r_comb: CirclePoint<BaseField>,
    g_hat_shift: &Vec<M31>,
    oods_rep: usize,
) -> Vec<BaseField> {
    let pol = rs.circ_lagrange_interp(&g_rs, false).unwrap();
    let pol_vals: Vec<BaseField> = xs
        .iter()
        .map(|x| pol.eval_circ_poly_at(&x.to_point()))
        .collect();
    let zpol = rs.circ_zpoly(None, true, Some(oods_rep)); // TODO: use `split_exts` to convert zpol to M31
    let zpol = zpol.circ_poly_to_int_poly().unwrap();

    let mut vals = vec![];
    for j in 0..2 * eval_size {
        let zzz: M31 = g_hat_shift.at(j);
        let aaa = pol_vals[j];
        let denom = zpol.eval_circ_poly_at(&xs[j].to_point());
        let a = (zzz - aaa) / denom;

        let geom_sum_res = ((xs[j].to_point() + r_comb).x).geom_sum(rs.len());

        let val = a * geom_sum_res;
        vals.push(val);
    }

    vals
}

fn open_merkle_tree<B: BackendForChannel<MC>, MC: MerkleChannel>(
    folding_param: usize,
    t_shifts: &Vec<u32>,
    t_conj: &Vec<u32>,
    folded_len: usize,
    eval_size: usize,
    tree: SimpleMerkleTree<B, MC::H>,
    vals: &Vec<BaseField>,
) -> (Vec<BaseField>, Vec<MerkleProof<MC::H>>) {
    let mut queried_index = vec![];
    for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
        for j in 0..folding_param {
            let index = (*t as usize) + (j * folded_len) + ((*k as usize) * eval_size);
            queried_index.push(index);
        }
    }

    let proofs = tree.generate_proofs(&queried_index);
    let queried_values = queried_index.iter().map(|i| vals[*i]).collect::<Vec<_>>();

    (queried_values, proofs)
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CircleStirProof<H: MerkleHasher> {
    pub all_betas: Vec<SecureField>,
    pub output_roots: Vec<H::Hash>,
    pub merkles_proofs: Vec<Vec<MerkleProof<H>>>,
    pub opened_values: Vec<Vec<BaseField>>,
    pub g_pol_final: Vec<BaseField>,
}

pub fn prove_low_degree<B: BackendForChannel<MC>, MC: MerkleChannel>(
    channel: &mut MC::C,
    coset: &Coset,
    eval_sizes: &Vec<usize>,
    max_deg_plus_1: usize,
    repetition_params: &Vec<usize>,
    folding_params: &Vec<usize>,
    values: &Vec<BaseField>,
    eval_offsets: &Vec<CirclePointIndex>,
) -> Result<CircleStirProof<MC::H>, String> {
    let mut coset = coset.clone();
    let ood_rep = 1;
    let mut output_roots = vec![];
    let mut all_betas = vec![];
    let mut output_merkle_proofs = vec![];
    let mut opened_values = vec![];

    let mut xs = coset.calculate_xs(eval_offsets[0]);

    if values.len() != xs.len() && xs.len() / 2 != eval_sizes[0] {
        return Err("values.len() != xs.len() && xs.len()/2 != eval_sizes[0]".to_owned());
    }

    let mut vals = values.to_owned();
    // TODO: to check if this is correct
    let mut merkle_tree_val = vals.clone();
    let mut merkle_tree = SimpleMerkleTree::<B, MC::H>::new(&vals);
    output_roots.push(merkle_tree.root());

    MC::mix_root(channel, merkle_tree.root());

    // TODO: not correct as we are not surd that the x and y are indeed on the circle
    // primitive root for M31 Gaussian(311014874, 1584694829)
    // CirclePoint mul by M31 value
    let rnd = channel.draw_felt();
    let mut r_fold = M31_CIRCLE_GEN.mul(rnd.0 .0 .0.into());
    let mut g_hat = vec![];

    let mut folded_len = 0;

    for i in 1..folding_params.len() + 1 {
        // # fold using r-fold
        if eval_sizes[i - 1] % folding_params[i - 1] != 0 {
            return Err("eval_sizes[i-1] % folding_params[i-1] != 0".to_owned());
        }

        folded_len = eval_sizes[i - 1] / folding_params[i - 1];
        let mut coset2 = coset.repeated_double(folded_len.ilog2());

        let xs2s = coset2.calculate_xs2s(folding_params[i - 1]);

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
            return Err("eval_sizes[i] % folded_len != 0".into());
        }
        if eval_sizes[i - 1] % eval_sizes[i] != 0 {
            return Err("self.eval_sizes[i-1] % self.eval_sizes[i] != 0".into());
        }

        let expand_factor = eval_sizes[i] / folded_len;
        let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];
        coset = coset.repeated_double(eval_size_scale.ilog2());
        coset2 = coset.repeated_double(expand_factor.ilog2());
        let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

        let g_hat_shift =
            shift_g_hat::<B, MC>(&g_hat, coset, expand_factor, p_offset, eval_offsets[i]);

        // let m2: MerkleProver<B, MC::H> = MerkleProver::commit(vec![&g_hat_shift.values]);
        let m2 = SimpleMerkleTree::<B, MC::H>::new(&g_hat_shift.values.to_cpu());
        output_roots.push(m2.root());

        MC::mix_root(channel, m2.root());

        xs = coset.calculate_xs(eval_offsets[i]);

        let r_outs: Vec<CirclePoint<SecureField>> = channel
            .draw_felts(ood_rep)
            .iter()
            .map(|v| (*v).into())
            .collect();

        let betas = get_betas::<B, MC>(&coset2, p_offset, &g_hat, &r_outs);

        channel.mix_felts(&betas);
        all_betas.append(&mut betas.clone());

        let r_comb;
        let t_vals;
        let t_shifts;
        let t_conj;
        (r_fold, r_comb, t_vals, t_shifts, t_conj) =
            generate_rnd_r_t_values::<MC>(channel, folded_len, repetition_params[i - 1]);

        if repetition_params[i - 1] % 2 != 0 {
            return Err("self.repetition_params[i-1]%2 != 0".to_owned());
        }

        let (rs, g_rs) = calculate_rs_and_g_rs(
            &r_outs, &betas, &t_shifts, &t_conj, &coset2, p_offset, &g_hat, folded_len,
        );

        let (queried_values, proofs) = open_merkle_tree(
            folding_params[i - 1],
            &t_shifts,
            &t_conj,
            folded_len,
            eval_sizes[i - 1],
            merkle_tree.clone(),
            &merkle_tree_val,
        );

        opened_values.push(queried_values);
        output_merkle_proofs.push(proofs);

        merkle_tree_val = g_hat_shift.clone().values.to_cpu();
        merkle_tree = m2;

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
    let g_pol = interpolate::<B, MC>(
        &coset.repeated_double((final_folding_param as u32).ilog2()),
        to_shift,
        &g_hat,
    );

    let numer = max_deg_plus_1;
    let denom: usize = folding_params.iter().product();
    let final_deg = numer / denom;

    let g_pol_coeffs: Vec<BaseField> = g_pol.coeffs.to_cpu();
    let (g_pol_final, g_pol_zeroes) = g_pol_coeffs.split_at(2 * final_deg + 1);

    let is_zero = g_pol_zeroes.iter().all(|x| *x == BaseField::zero());
    if !is_zero {
        return Err("g_pol_final is not zero. something is not right".to_string());
    }

    let g_pol_final_secure: Vec<QM31> = g_pol_final
        .iter()
        .map(|g| SecureField::from_single_m31(*g))
        .collect();

    channel.mix_felts(&g_pol_final_secure);

    let (t_vals, t_shifts, t_conj) = generate_rnd_t_values::<MC>(
        channel,
        folded_len,
        repetition_params[repetition_params.len() - 1],
    );

    let (queried_values, proof) = open_merkle_tree(
        folding_params[folding_params.len() - 1],
        &t_shifts,
        &t_conj,
        folded_len,
        eval_sizes[folding_params.len() - 1],
        merkle_tree,
        &merkle_tree_val.to_cpu(),
    );

    let indexes = proof.iter().map(|p| p.indices).collect::<Vec<_>>();
    opened_values.push(queried_values);
    output_merkle_proofs.push(proof);

    Ok(CircleStirProof {
        all_betas,
        output_roots,
        merkles_proofs: output_merkle_proofs,
        opened_values,
        g_pol_final: g_pol_final.to_vec(),
    })
}

#[allow(unused_mut)]
pub fn verify_low_degree_proof<B: BackendForChannel<MC>, MC: MerkleChannel>(
    channel: &mut MC::C,
    proof: &CircleStirProof<MC::H>,
    coset: &Coset,
    eval_sizes: &Vec<usize>,
    repetition_params: &Vec<usize>,
    folding_params: &Vec<usize>,
    eval_offsets: &Vec<CirclePointIndex>,
    log_size: usize,
) -> Result<(), String> {
    let oods_rep = 1;
    let mut opened_values = proof.opened_values.clone();
    let mut output_roots = proof.output_roots.clone();
    let mut output_merkle_proofs = proof.merkles_proofs.clone();
    let mut all_betas = proof.all_betas.clone();
    let mut log_size = log_size;
    let maxdeg_plus_1 = 1 << log_size;

    if folding_params.len() != eval_offsets.len()
        || folding_params.len() != eval_sizes.len()
        || folding_params.len() != repetition_params.len()
    {
        return Err("folding_params.len() != eval_offsets.len() || folding_params.len() != eval_sizes.len() || folding_params.len() != repetition_params.len()".to_owned());
    }

    let mut coset = coset.clone();

    if coset.repeated_double(eval_sizes[0].ilog2()).step_size != CirclePointIndex(0) {
        return Err(
            "coset.repeated_double(eval_sizes[0].ilog2()).step_size != CirclePointIndex(0) "
                .to_owned(),
        );
    }

    // TODO fix self.modulus - 1
    // assert f.exp(rt,self.eval_sizes[0]//2) == Gaussian(self.modulus - 1,0)
    if coset.repeated_double((eval_sizes[0] / 2).ilog2()).step_size
        != CirclePointIndex((P as usize + 1) / 2)
    {
        return Err(
            "coset.repeated_double(eval_sizes[0] / 2).initial_index != CirclePointIndex(0) "
                .to_owned(),
        );
    }

    let mut m_root = output_roots.remove(0);
    MC::mix_root(channel, m_root);
    let rnd = channel.draw_felt();
    let mut r_fold = M31_CIRCLE_GEN.mul(rnd.0 .0 .0.into());
    let mut r_comb = CirclePoint::<BaseField>::zero();
    let mut rs = vec![];
    let mut zpol = [vec![], vec![]];
    let mut g_rs = vec![];
    let mut pol = [vec![], vec![]];

    for i in 1..folding_params.len() {
        if eval_sizes[i - 1] % folding_params[i - 1] != 0 {
            return Err("eval_sizes[i-1] % folding_params[i-1] != 0".to_owned());
        }

        let folded_len = eval_sizes[i - 1] / folding_params[i - 1];
        if eval_sizes[i] % folded_len != 0 {
            return Err("eval_sizes[i] % folded_len != 0".to_owned());
        }
        let expand_factor = eval_sizes[i] / folded_len;
        if eval_sizes[i - 1] % eval_sizes[i] != 0 {
            return Err("eval_sizes[i-1] % eval_sizes[i] != 0".to_owned());
        }
        let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];

        let coset_new = coset.repeated_double(eval_size_scale.ilog2());
        let coset2 = coset_new.repeated_double(expand_factor.ilog2());
        let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

        let m2_root = output_roots.remove(0);

        MC::mix_root(channel, m2_root);

        let r_outs: Vec<CirclePoint<SecureField>> = channel
            .draw_felts(oods_rep)
            .iter()
            .map(|v| (*v).into())
            .collect();
        let temp_betas = all_betas.split_off(oods_rep);
        let betas = all_betas;
        all_betas = temp_betas;

        channel.mix_felts(&betas);

        let r_fold_new;
        let r_comb_new;
        let t_vals;
        let t_shifts;
        let t_conj;
        (r_fold_new, r_comb_new, t_vals, t_shifts, t_conj) =
            generate_rnd_r_t_values::<MC>(channel, folded_len, repetition_params[i - 1]);

        let rs_new = calculate_rs(&r_outs, &t_shifts, &t_conj, &coset2, p_offset);

        let temp_coset2 = coset.repeated_double(folded_len.ilog2());
        let xs2s = temp_coset2.calculate_xs2s(folding_params[i - 1]);

        let output_branch = output_merkle_proofs.remove(0);
        let values = opened_values.remove(0);

        let verify_res = verify_many_proof(&output_branch, m_root, &values);
        if !verify_res {
            return Err("verify proof failed".to_owned());
        }

        let mut vals = values;

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
        m_root = m2_root;
        r_fold = r_fold_new;
        r_comb = r_comb_new;
        rs = rs_new;
        zpol = rs.circ_zpoly(None, true, Some(oods_rep));
        g_rs = betas
            .into_iter()
            .chain(g_hat.into_iter().map(|x| QM31::from_single_m31(x)))
            .collect();
        pol = rs.circ_lagrange_interp(&g_rs, false).unwrap();
    }

    let denom: usize = folding_params.iter().product();
    let final_deg = maxdeg_plus_1 / denom;

    if eval_sizes[eval_sizes.len() - 1] % folding_params[folding_params.len() - 1] != 0 {
        return Err(
            "eval_sizes[eval_sizes.len() - 1] % folding_params[folding_params.len() - 1] != 0"
                .to_owned(),
        );
    }
    let folded_len = eval_sizes[eval_sizes.len() - 1] / folding_params[folding_params.len() - 1];
    let coset2 = coset.repeated_double(folding_params[folding_params.len() - 1].ilog2());

    let g_pol_final_secure: Vec<QM31> = proof
        .g_pol_final
        .iter()
        .map(|g| SecureField::from_single_m31(*g))
        .collect();

    channel.mix_felts(&g_pol_final_secure);

    let (t_vals, t_shifts, t_conj) = generate_rnd_t_values::<MC>(
        channel,
        folded_len,
        repetition_params[repetition_params.len() - 1],
    );

    let coset3 = coset.repeated_double(folded_len.ilog2());
    let xs2s = coset3.calculate_xs2s(folding_params[folding_params.len() - 1]);

    // let root = output_roots.remove(0);
    let output_branch = output_merkle_proofs.remove(0);
    let values = opened_values.remove(0);

    let verify_res = verify_many_proof(&output_branch, m_root, &values);
    if !verify_res {
        return Err("verify proof failed".to_owned());
    }

    let mut vals = values;

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

            let d = (*v - pol.eval_circ_poly_at(&x.to_point()))
                / zpol.eval_circ_poly_at(&x.to_secure_field_point());

            let m = d.0 .0 * ((x.to_point() + r_comb).x).geom_sum(rs.len());
            v_s.push(m);
        }

        let lagrange_interp = &xs2s[t_conj[k] as usize]
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

        let mut coeffs: Vec<BaseField> = proof.g_pol_final.iter().map(|x| *x).collect();
        if !coeffs.len().is_power_of_two() {
            let next_power_of_two = coeffs.len().next_power_of_two();
            coeffs.resize(next_power_of_two, BaseField::from(0));
        }
        let rhs = CirclePoly::<B>::new(coeffs.iter().map(|x| *x).collect())
            .eval_at_point(offset.to_secure_field_point())
            .0
             .0;

        if lhs != rhs {
            return Err("lhs != rhs".to_owned());
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{calculate_g_hat, calculate_rs_and_g_rs, fold_val};
    use crate::core::backend::CpuBackend;
    use crate::core::channel::MerkleChannel;
    use crate::core::circle::{CirclePoint, CirclePointIndex};
    use crate::core::circle_fft::{evaluate, get_betas, interpolate, shift_g_hat};
    use crate::core::fields::m31::{BaseField, M31};
    use crate::core::fields::qm31::{SecureField, QM31};
    use crate::core::fields::{
        AllConjugate, CircPolyInterpolation, FieldCircPolyOps, FieldPolyOps,
    };
    use crate::core::pcs::PcsConfig;
    use crate::core::poly::circle::{CanonicCoset, CirclePoly};
    use crate::core::vcs::blake2_merkle::Blake2sMerkleChannel;
    use crate::core::vcs::prover::MerkleProver;
    use crate::core::vcs::verifier::MerkleVerifier;

    #[test]
    fn test_calculate_xs2s() {
        let log_size = 3;
        let coset = CanonicCoset::new(log_size).coset;
        let folding_param = 1 << 2;
        let xs2s = coset.calculate_xs2s(folding_param);

        let xs2s_points_0: Vec<CirclePoint<M31>> = xs2s[0].iter().map(|x| x.to_point()).collect();
        let xs2s_points_1: Vec<CirclePoint<M31>> = xs2s[1].iter().map(|x| x.to_point()).collect();

        assert_eq!(
            xs2s_points_0,
            vec![
                CirclePoint {
                    x: M31(1),
                    y: M31(0)
                },
                CirclePoint {
                    x: M31(32768),
                    y: M31(2147450879)
                },
                CirclePoint {
                    x: M31(0),
                    y: M31(2147483646)
                },
                CirclePoint {
                    x: M31(2147450879),
                    y: M31(2147450879)
                },
                CirclePoint {
                    x: M31(2147483646),
                    y: M31(0)
                },
                CirclePoint {
                    x: M31(2147450879),
                    y: M31(32768)
                },
                CirclePoint {
                    x: M31(0),
                    y: M31(1)
                },
                CirclePoint {
                    x: M31(32768),
                    y: M31(32768)
                }
            ]
        );
        assert_eq!(
            xs2s_points_1,
            vec![
                CirclePoint {
                    x: M31(1),
                    y: M31(0)
                },
                CirclePoint {
                    x: M31(32768),
                    y: M31(32768)
                },
                CirclePoint {
                    x: M31(0),
                    y: M31(1)
                },
                CirclePoint {
                    x: M31(2147450879),
                    y: M31(32768)
                }
            ]
        );
    }

    #[test]
    fn test_conj() {
        let index = CirclePointIndex(5);
        let point = index.to_point();

        let index_conj = index.conj();
        let conj_point = index_conj.to_point();

        assert_eq!(
            conj_point,
            CirclePoint::<M31> {
                x: point.x,
                y: -point.y,
            }
        );
    }

    #[test]
    fn test_calculate_xs() {
        let log_size = 3;
        let coset = CanonicCoset::new(log_size).coset;
        let offset = CirclePointIndex(1);
        let offset_point = offset.to_point();
        let xs = coset.calculate_xs(offset);
        let xs_points: Vec<CirclePoint<M31>> = xs.iter().map(|x| x.to_point()).collect();

        assert_eq!(
            xs_points,
            vec![
                CirclePoint {
                    x: M31(2),
                    y: M31(1268011823)
                },
                CirclePoint {
                    x: M31(697879444),
                    y: M31(697748372)
                },
                CirclePoint {
                    x: M31(1268011823),
                    y: M31(2147483645)
                },
                CirclePoint {
                    x: M31(697748372),
                    y: M31(1449604203)
                },
                CirclePoint {
                    x: M31(2147483645),
                    y: M31(879471824)
                },
                CirclePoint {
                    x: M31(1449604203),
                    y: M31(1449735275)
                },
                CirclePoint {
                    x: M31(879471824),
                    y: M31(2)
                },
                CirclePoint {
                    x: M31(1449735275),
                    y: M31(697879444)
                },
                CirclePoint {
                    x: M31(2),
                    y: M31(879471824)
                },
                CirclePoint {
                    x: M31(697879444),
                    y: M31(1449735275)
                },
                CirclePoint {
                    x: M31(1268011823),
                    y: M31(2)
                },
                CirclePoint {
                    x: M31(697748372),
                    y: M31(697879444)
                },
                CirclePoint {
                    x: M31(2147483645),
                    y: M31(1268011823)
                },
                CirclePoint {
                    x: M31(1449604203),
                    y: M31(697748372)
                },
                CirclePoint {
                    x: M31(879471824),
                    y: M31(2147483645)
                },
                CirclePoint {
                    x: M31(1449735275),
                    y: M31(1449604203)
                }
            ]
        );
    }

    #[test]
    fn test_calculate_g_hat() {
        let log_size = 3;
        let eval_size = 1 << log_size;
        let folding_param = 2;
        let folded_len: usize = eval_size / folding_param;
        let r_fold = CirclePointIndex(1).to_point();
        let coset = CanonicCoset::new(log_size).coset;
        let coset2 = coset.repeated_double(folded_len.ilog2());

        let vals: Vec<M31> = (0..2 * eval_size).map(|x| BaseField::from(x)).collect();

        let xs = coset.calculate_xs(CirclePointIndex(0));
        let xs2s = coset2.calculate_xs2s(folding_param);

        let g_hat = calculate_g_hat(
            folded_len,
            folding_param,
            eval_size,
            r_fold,
            &vals,
            &xs2s,
            &xs,
        );

        assert_eq!(
            g_hat,
            vec![
                M31(2147483645),
                M31(1395496747),
                M31(388540003),
                M31(1395758893),
                M31(6),
                M31(751724770),
                M31(1758943660),
                M31(751986916)
            ]
        );
    }

    #[test]
    fn test_shift_g_hat() {
        let log_size = 3;
        let expand_factor = 2;
        let eval_size: i32 = 1 << log_size + 1; // because the canonic coset uses half coset hence we need to double the eval_size
        let coset = CanonicCoset::new(log_size + (expand_factor as usize).ilog2()).coset;
        let vals: Vec<M31> = (0..eval_size).map(|x| BaseField::from(x)).collect();
        let p_offset = CirclePointIndex(1);
        let p_offset_point = p_offset.to_point();
        let eval_offset = CirclePointIndex(2);
        let eval_offset_point = eval_offset.to_point();

        let g_hat_shift = shift_g_hat::<CpuBackend, Blake2sMerkleChannel>(
            &vals,
            coset,
            expand_factor as usize,
            p_offset,
            eval_offset,
        );

        assert_eq!(
            g_hat_shift.values,
            vec![
                M31(1202987316),
                M31(1994628606),
                M31(62953673),
                M31(1676200487),
                M31(1232855071),
                M31(1541252791),
                M31(649945473),
                M31(179108572),
                M31(611770365),
                M31(224890177),
                M31(509951501),
                M31(945953568),
                M31(1113918000),
                M31(2115474593),
                M31(1056865314),
                M31(2061113789),
                M31(1203288388),
                M31(1994327534),
                M31(63254745),
                M31(1675899415),
                M31(1233156143),
                M31(1540951719),
                M31(650246545),
                M31(178807500),
                M31(612071437),
                M31(224589105),
                M31(510252573),
                M31(945652496),
                M31(1114219072),
                M31(2115173521),
                M31(1057166386),
                M31(2060812717),
            ]
        );
    }

    #[test]
    fn test_get_betas() {
        let log_size = 3;
        let coset = CanonicCoset::new(log_size).coset();
        let offset = CirclePointIndex(1);
        let offset_point = offset.to_point();
        let g_hat = (0..1 << (log_size + 1)).map(|x| M31(x)).collect();
        let rnds = vec![
            QM31::from_u32_unchecked(1, 2, 3, 4),
            QM31::from_u32_unchecked(5, 6, 7, 8),
            QM31::from_u32_unchecked(9, 10, 11, 12),
        ];
        let r_outs: Vec<CirclePoint<SecureField>> = rnds.iter().map(|v| (*v).into()).collect();

        let betas = get_betas::<CpuBackend, Blake2sMerkleChannel>(&coset, offset, &g_hat, &r_outs);
        // [((1743753900, 1717223839), (1032320333, 1015200802)), ((1260623339, 1950301647),
        // (805251682, 956842345)), ((878227697, 639636854), (811147145, 1122453360))]

        assert_eq!(
            betas,
            vec![
                QM31::from_u32_unchecked(1743753900, 1717223839, 1032320333, 1015200802),
                QM31::from_u32_unchecked(1260623339, 1950301647, 805251682, 956842345),
                QM31::from_u32_unchecked(878227697, 639636854, 811147145, 1122453360)
            ]
        )
    }

    #[test]
    fn test_get_mul_cycle() {
        let log_size = 3;
        let config = PcsConfig::default();
        let coset = CanonicCoset::new(log_size).circle_domain().half_coset;

        let xs = coset.get_mul_cycle(CirclePointIndex(0));
        let xs_points: Vec<CirclePoint<M31>> = xs.iter().map(|x| x.to_point()).collect();

        // [(1, 0), (0, 2147483646), (2147483646, 0), (0, 1)]
        assert_eq!(
            xs_points,
            vec![
                CirclePoint {
                    x: M31(1),
                    y: M31(0)
                },
                CirclePoint {
                    x: M31(0),
                    y: M31(2147483646)
                },
                CirclePoint {
                    x: M31(2147483646),
                    y: M31(0)
                },
                CirclePoint {
                    x: M31(0),
                    y: M31(1)
                }
            ]
        );
    }

    #[test]
    fn test_base_field_all_conj() {
        // will return itself
        let val = BaseField::from(123);
        let conjs = val.all_conj();

        assert_eq!(conjs.len(), 1);
        assert_eq!(conjs[0], val);
    }

    #[test]
    #[ignore]
    fn test_cm31_all_conj() {
        todo!();
        // return [self,CM(self.a,-self.b,self.modulus)]
        // let val = CM31::from_m31(BaseField::from(123), BaseField::from(321));
        // let conjs = val.all_conj();

        // assert_eq!(conjs.len(), 2);
        // assert_eq!(conjs[0], val);
        // assert_eq!(
        //     conjs[1],
        //     CM31::from_m31(BaseField::from(123), BaseField::from(-321))
        // )
    }

    #[test]
    #[ignore]
    fn test_qm31_all_conj() {
        todo!();
        // // conj = [self,QM(self.A,-self.B,self.param)]
        // // return conj + [c**self.A.modulus for c in conj] # applying frobenius
        // let base_1 = BaseField::from(123);
        // let base_2 = BaseField::from(234);
        // let base_3 = BaseField::from(345);
        // let base_4 = BaseField::from(567);

        // let val = QM31::from_m31(base_1, base_2, base_3, base_4);
        // let conjs = val.all_conj();

        // assert_eq!(conjs.len(), 4);
        // assert_eq!(conjs[0], val);
        // assert_eq!(conjs[1], QM31::from_m31(base_1, base_2, -base_3, -base_4));
        // // assert for all remaining conjugates
    }

    #[test]
    fn test_line() {
        let pt1 = CirclePointIndex(1).to_point();
        let pt2 = CirclePointIndex(2).to_point();

        let line_res = pt1.line(pt2);
        assert_eq!(
            line_res,
            [
                vec![M31(1464384553), M31(2049297282)],
                vec![M31(2147483646)]
            ]
        );
    }

    #[test]
    fn test_mul_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = a.mul_polys(&b);
        assert_eq!(res, vec![M31(35), M31(82), M31(48)]);
    }

    #[test]
    fn test_add_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = a.add_polys(&b);
        assert_eq!(res, vec![M31(12), M31(14)]);
    }

    #[test]
    fn test_sub_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = a.sub_polys(&b);
        assert_eq!(res, vec![M31(2147483645), M31(2147483645)]);
    }

    #[test]
    fn test_mul_circ_polys() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = [vec![M31(7), M31(8)], vec![M31(9), M31(10)]];

        let res = a.mul_circ_polys(&b);
        assert_eq!(
            res,
            [
                vec![M31(98), M31(224), M31(65), M31(2147483505), M31(2147483567)],
                vec![M31(94), M31(216), M31(124)]
            ]
        );
    }

    #[test]
    fn test_add_circ_polys() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = [vec![M31(7), M31(8)], vec![M31(9), M31(10)]];

        let res = a.add_circ_polys(&b);

        // [[12, 14], [16, 18]]
        assert_eq!(res, [vec![M31(12), M31(14)], vec![M31(16), M31(18)]]);
    }

    #[test]
    fn test_sub_circ_polys() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = [vec![M31(7), M31(8)], vec![M31(9), M31(10)]];

        let res = a.sub_circ_polys(&b);
        assert_eq!(
            res,
            [
                vec![M31(2147483645), M31(2147483645)],
                vec![M31(2147483645), M31(2147483645)]
            ]
        );
    }

    #[test]
    fn test_mul_circ_by_const() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = M31(7);

        let res = a.mul_circ_by_const(&b);
        assert_eq!(res, [vec![M31(35), M31(42)], vec![M31(49), M31(56)]]);
    }

    #[test]
    fn test_circ_zpoly_split_exts_false() {
        let a = vec![
            CirclePointIndex(1).to_point(),
            CirclePointIndex(2).to_point(),
            CirclePointIndex(3).to_point(),
        ];
        let res = a.circ_zpoly(None, false, None);
        assert_eq!(
            res,
            [
                vec![M31(1566776379), M31(277737251), M31(98186365)],
                vec![M31(2147483621), M31(1)]
            ]
        );
    }

    #[test]
    fn test_circ_zpoly_split_exts_true() {
        let a = vec![
            CirclePoint {
                x: QM31::from_single_m31(M31(2)),
                y: QM31::from_single_m31(M31(1268011823)),
            },
            CirclePoint {
                x: QM31::from_single_m31(M31(2020439472)),
                y: QM31::from_single_m31(M31(224065515)),
            },
            CirclePoint {
                x: QM31::from_single_m31(M31(426051698)),
                y: QM31::from_single_m31(M31(419694706)),
            },
            CirclePoint {
                x: QM31::from_single_m31(M31(1055058706)),
                y: QM31::from_single_m31(M31(919471560)),
            },
            CirclePoint {
                x: QM31::from_single_m31(M31(141701737)),
                y: QM31::from_single_m31(M31(2147483550)),
            },
        ];

        let res = a.circ_zpoly(None, true, Some(1));

        assert_eq!(
            res,
            [
                vec![
                    QM31::from_single_m31(M31(2096851543)),
                    QM31::from_single_m31(M31(344681428)),
                    QM31::from_single_m31(M31(1656326039)),
                    QM31::from_single_m31(M31(257962589)),
                    QM31::from_single_m31(M31(1027629259)),
                ],
                vec![
                    QM31::from_single_m31(M31(1583685796)),
                    QM31::from_single_m31(M31(326006918)),
                    QM31::from_single_m31(M31(633712382)),
                    QM31::from_single_m31(M31(1551165002))
                ]
            ]
        )
        // [[2096851543, 344681428, 1656326039, 257962589, 1027629259], [1583685796, 326006918,
        // 633712382, 1551165002]]
    }

    #[test]
    fn test_eval_poly_at() {
        let poly = vec![M31(1), M31(2), M31(3)];
        let pt = M31(2);
        let res = poly.eval_poly_at(&pt);
        assert_eq!(res, M31(17));
    }

    #[test]
    fn test_eval_circ_poly_at() {
        let poly = [vec![M31(1), M31(2), M31(3)], vec![M31(4), M31(5), M31(6)]];
        let pt = CirclePointIndex(1).to_point();
        let res = poly.eval_circ_poly_at(&pt);
        assert_eq!(res, M31(939809057));
    }

    #[test]
    fn test_circ_lagrange_interp() {
        let pts = vec![
            CirclePointIndex(2),
            CirclePointIndex(3),
            CirclePointIndex(4),
        ]
        .iter()
        .map(|x| x.to_point())
        .collect::<Vec<_>>();
        let values = vec![M31(1), M31(2), M31(3)];
        let res = pts.circ_lagrange_interp(&values, false).unwrap();
        assert_eq!(res, [vec![M31(2), M31(2147483632)], vec![M31(463810318)]]);
    }

    #[test]
    fn test_fft_ifft_with_offset() {
        let poly_log_length = 4;
        let offset: CirclePointIndex = CirclePointIndex(2);
        let offset_point = offset.to_point();
        let coset = CanonicCoset::new(poly_log_length).coset;
        let values: Vec<M31> = (0..1 << (poly_log_length + 1)).map(|x| M31(x)).collect();
        let poly = interpolate::<CpuBackend, Blake2sMerkleChannel>(&coset, offset, &values);
        let coeffs = poly.clone().coeffs;

        assert_eq!(
            coeffs,
            [
                M31(1073741839),
                M31(0),
                M31(1529805092),
                M31(0),
                M31(1391306209),
                M31(0),
                M31(1915085074),
                M31(0),
                M31(1631102365),
                M31(0),
                M31(550574923),
                M31(0),
                M31(768417018),
                M31(0),
                M31(1061520795),
                M31(0),
                M31(683740790),
                M31(0),
                M31(1545654070),
                M31(0),
                M31(681605261),
                M31(0),
                M31(492787859),
                M31(0),
                M31(822270530),
                M31(0),
                M31(1539733550),
                M31(0),
                M31(1700331639),
                M31(0),
                M31(1375452669),
                M31(982499677)
            ]
        );

        let evals = evaluate::<CpuBackend, Blake2sMerkleChannel>(poly, &coset, offset);
        assert_eq!(evals.values, values);
    }
    // circ_poly_to_int_poly

    // TODO: to remove this test, tested to be correct
    #[test]
    fn test_eval_at_point_secure_field() {
        let rnd_point = QM31::from_u32_unchecked(1, 2, 3, 4);
        let r_out: CirclePoint<SecureField> = rnd_point.into();

        let poly = CirclePoly::<CpuBackend>::new(vec![
            M31(1073741831),
            M31(0),
            M31(142172079),
            M31(0),
            M31(1031667956),
            M31(0),
            M31(1966318798),
            M31(0),
            M31(1429038289),
            M31(0),
            M31(251819275),
            M31(0),
            M31(1173966850),
            M31(0),
            M31(772153390),
            M31(613376015),
        ]);

        let e = poly.eval_at_point(r_out.into());
        println!("{:?}", e);
        // ((1257134414, 567605011), (1327534562, 118934739))
    }

    #[test]
    fn test_calculate_rs_and_g_rs() {
        let log_size = 3;
        let coset = CanonicCoset::new(log_size).coset();
        let offset = CirclePointIndex(1);
        let offset_point = offset.to_point();
        let g_hat = (0..1 << (log_size + 1)).map(|x| M31(x)).collect();
        let rnds = vec![
            QM31::from_u32_unchecked(1, 2, 3, 4),
            QM31::from_u32_unchecked(5, 6, 7, 8),
            QM31::from_u32_unchecked(9, 10, 11, 12),
        ];
        let r_outs: Vec<CirclePoint<SecureField>> = rnds.iter().map(|v| (*v).into()).collect();
        let betas = get_betas::<CpuBackend, Blake2sMerkleChannel>(&coset, offset, &g_hat, &r_outs);

        let folding_param = 2;
        let folded_len = 1 << log_size / folding_param;
        let t_vals: Vec<u32> = vec![22018, 2192, 23030, 13311]
            .iter()
            .map(|&t| t % ((2 * folded_len) as u32))
            .collect();
        let t_shifts: Vec<u32> = t_vals.iter().map(|&t| (t / 2)).collect();
        let t_conj: Vec<u32> = t_vals.iter().map(|&t| (t % (2))).collect();

        let expand_factor = 2 as usize;
        let coset2 = coset.repeated_double(expand_factor.ilog2());
        let offset_point2 = coset2.shift(offset).initial;

        let (rs, g_rs) = calculate_rs_and_g_rs(
            &r_outs, &betas, &t_shifts, &t_conj, &coset2, offset, &g_hat, folded_len,
        );

        assert_eq!(
            rs,
            vec![
                CirclePoint::<SecureField> {
                    x: QM31::from_u32_unchecked(2001365350, 428420505, 1868078972, 2005504680),
                    y: QM31::from_u32_unchecked(1719063144, 2001365349, 141978971, 1868078969),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_u32_unchecked(1894965280, 1720927558, 1413715516, 1452232956),
                    y: QM31::from_u32_unchecked(426556095, 1894965275, 695250699, 1413715509),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_u32_unchecked(1462087839, 2027728257, 1661132873, 884790667),
                    y: QM31::from_u32_unchecked(119755400, 1462087830, 1262692992, 1661132862),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_single_m31(M31(1268011823)),
                    y: QM31::from_single_m31(M31(2147483645)),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_single_m31(M31(2)),
                    y: QM31::from_single_m31(M31(1268011823)),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_single_m31(M31(1268011823)),
                    y: QM31::from_single_m31(M31(2147483645)),
                },
                CirclePoint::<SecureField> {
                    x: QM31::from_single_m31(M31(1268011823)),
                    y: QM31::from_single_m31(M31(2)),
                },
            ]
        );

        assert_eq!(
            g_rs,
            vec![
                QM31::from_u32_unchecked(1743753900, 1717223839, 1032320333, 1015200802),
                QM31::from_u32_unchecked(1260623339, 1950301647, 805251682, 956842345),
                QM31::from_u32_unchecked(878227697, 639636854, 811147145, 1122453360),
                QM31::from_single_m31(M31(1)),
                QM31::from_single_m31(M31(0)),
                QM31::from_single_m31(M31(1)),
                QM31::from_single_m31(M31(3))
            ]
        );
    }

    #[test]
    fn test_fold_val() {
        let log_size = 4;
        let mut coset = CanonicCoset::new(log_size + 2).coset;

        let ori_eval_size = 1 << (log_size + 2);
        let eval_size = ori_eval_size / 2;

        let ori_eval_offset = CirclePointIndex(1);
        let ori_eval_offset_point = ori_eval_offset.to_point();
        let eval_offset = coset.step_size + ori_eval_offset;
        let eval_offset_point = eval_offset.to_point();
        let xs = coset.calculate_xs(ori_eval_offset);
        let xs_points: Vec<CirclePoint<M31>> = xs.iter().map(|x| x.to_point()).collect();

        let folding_param = 4;
        let folded_len: usize = ori_eval_size / folding_param;
        let r_fold = CirclePointIndex(1).to_point(); // random point
        let mut coset2 = coset.repeated_double(folded_len.ilog2());

        let xs2s = coset2.calculate_xs2s(folding_param);
        let xs2s_points_0: Vec<CirclePoint<M31>> = xs2s[0].iter().map(|x| x.to_point()).collect();
        let xs2s_points_1: Vec<CirclePoint<M31>> = xs2s[1].iter().map(|x| x.to_point()).collect();

        let vals: Vec<M31> = (0..2 * ori_eval_size).map(|x| BaseField::from(x)).collect();

        let g_hat = calculate_g_hat(
            folded_len,
            folding_param,
            ori_eval_size,
            r_fold,
            &vals,
            &xs2s,
            &xs,
        );

        let eval_size_next = ori_eval_size / 2;
        let expand_factor = eval_size / folded_len;
        let eval_size_scale = ori_eval_size / eval_size;
        coset = coset.repeated_double(eval_size_scale.ilog2());
        let expand_factor_log = expand_factor.ilog2();
        coset2 = coset.repeated_double(expand_factor.ilog2());
        let p_offset = ori_eval_offset * folding_param;
        let p_offset_point = p_offset.to_point();

        let g_hat_shift = shift_g_hat::<CpuBackend, Blake2sMerkleChannel>(
            &g_hat,
            coset,
            expand_factor as usize,
            p_offset,
            eval_offset,
        );

        let rnds = vec![
            QM31::from_u32_unchecked(1, 2, 3, 4),
            QM31::from_u32_unchecked(5, 6, 7, 8),
            QM31::from_u32_unchecked(9, 10, 11, 12),
        ];
        let r_outs: Vec<CirclePoint<SecureField>> = rnds.iter().map(|v| (*v).into()).collect();

        let betas =
            get_betas::<CpuBackend, Blake2sMerkleChannel>(&coset2, p_offset, &g_hat, &r_outs);

        let t_vals: Vec<u32> = vec![22018, 2192, 23030, 13311]
            .iter()
            .map(|&t| t % ((2 * folded_len) as u32))
            .collect();
        let t_shifts: Vec<u32> = t_vals.iter().map(|&t| (t / 2)).collect();
        let t_conj: Vec<u32> = t_vals.iter().map(|&t| (t % (2))).collect();

        let (rs, g_rs) = calculate_rs_and_g_rs(
            &r_outs, &betas, &t_shifts, &t_conj, &coset2, p_offset, &g_hat, folded_len,
        );

        println!("rs: {:?}", rs);
        println!("g_rs: {:?}", g_rs);

        let folded_vals = fold_val(&rs, &g_rs, &xs, eval_size, r_fold, &g_hat_shift, 1);

        assert_eq!(
            folded_vals,
            vec![
                M31(1542920072),
                M31(757127436),
                M31(964470750),
                M31(942787347),
                M31(507842288),
                M31(1448015383),
                M31(1975452888),
                M31(1470820197),
                M31(1247357182),
                M31(1605441066),
                M31(1157611370),
                M31(1728126083),
                M31(2076812931),
                M31(120685567),
                M31(73792063),
                M31(138466685),
                M31(1408383802),
                M31(609731456),
                M31(675050321),
                M31(1004400754),
                M31(765051680),
                M31(1312352009),
                M31(951846940),
                M31(98879838),
                M31(1368445810),
                M31(1364099675),
                M31(1383613746),
                M31(1746577100),
                M31(659489686),
                M31(1560286765),
                M31(183744761),
                M31(797313211),
                M31(1094353584),
                M31(466389699),
                M31(1206566795),
                M31(892550422),
                M31(1610998386),
                M31(77420654),
                M31(303493718),
                M31(765916727),
                M31(464795491),
                M31(1923141863),
                M31(1340187209),
                M31(596507134),
                M31(738411156),
                M31(800066080),
                M31(1279015926),
                M31(1465898922),
                M31(1531866448),
                M31(417028292),
                M31(2101977463),
                M31(547401174),
                M31(135124960),
                M31(301905297),
                M31(2017130685),
                M31(32449442),
                M31(1217102802),
                M31(1410326073),
                M31(1756599916),
                M31(1501273479),
                M31(1783082249),
                M31(558464741),
                M31(21028768),
                M31(641020441)
            ]
        )
    }

    #[test]
    fn test_merkle_tree() {
        let log_size: usize = 4;
        let values: Vec<BaseField> = (0..(1 << log_size))
            .map(|x| BaseField::from(2 * x))
            .collect();
        let queried_index: Vec<usize> = vec![0, 1, 2, 3];
        let mut queries = BTreeMap::<usize, Vec<usize>>::new();
        queries.insert(log_size, queried_index.clone());

        let merkle_tree_val = values.iter().map(|x| *x).collect();
        let merkle_tree: MerkleProver<CpuBackend, <Blake2sMerkleChannel as MerkleChannel>::H> =
            MerkleProver::commit(vec![&merkle_tree_val]);

        let mut queries = BTreeMap::<u32, Vec<usize>>::new();
        queries.insert(merkle_tree_val.len().ilog2(), queried_index);

        let (values, decommitment) = merkle_tree.decommit(queries.clone(), vec![&merkle_tree_val]);
        // let decommitment = merkle_tree.decommit(queries, vec![values]);
        // println!("{:?}", decommitment);

        let verifier = MerkleVerifier::<<Blake2sMerkleChannel as MerkleChannel>::H>::new(
            merkle_tree.root(),
            vec![log_size as u32],
        );

        let res = verifier.verify(queries, values, decommitment);
        assert_eq!(res.is_ok(), true);
    }
}

// all_conj
// qm31
// circlepoint(basefield)
// circlepoint(cm31)
// circlepoint(qm31)
