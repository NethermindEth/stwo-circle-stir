#![allow(unused_variables)]
#![allow(unused_assignments)]

use std::collections::BTreeMap;
use std::vec;

use itertools::max;
use num_traits::Zero;

use super::backend::{BackendForChannel, Column, ColumnOps};
use super::channel::{Channel, MerkleChannel};
use super::circle::{CirclePoint, CirclePointIndex, Coset, M31_CIRCLE_GEN};
use super::fields::cm31::CM31;
use super::fields::m31::{BaseField, M31, P};
use super::fields::qm31::{SecureField, QM31};
use super::fields::{Field, FieldExpOps};
use super::poly::circle::{CircleDomain, CircleEvaluation, CirclePoly};
use super::poly::NaturalOrder;
use super::vcs::prover::{MerkleDecommitment, MerkleProver};
use crate::core::fields::ComplexConjugate;

fn calculate_xs2s(coset: Coset, folding_param: usize) -> [Vec<CirclePointIndex>; 2] {
    let mut xs2s: [Vec<CirclePointIndex>; 2] = [vec![], vec![]];
    xs2s[0] = coset.get_mul_cycle(CirclePointIndex(0));
    xs2s[1] = (0..folding_param)
        .map(|j| xs2s[0][xs2s[0].len() - j - 1])
        .collect();

    xs2s
}

fn calculate_xs(coset: &Coset, eval_offset: CirclePointIndex) -> Vec<CirclePointIndex> {
    let mut xs = coset.get_mul_cycle(eval_offset);
    let mut xs_conj: Vec<CirclePointIndex> = xs.iter().map(|x| x.conj()).collect();
    xs.append(&mut xs_conj);

    xs
}

fn calculate_g_hat(
    folded_len: usize,
    folding_param: usize,
    eval_size: usize,
    r_fold: CirclePoint<BaseField>,
    vals: &Vec<BaseField>,
    xs2s: &[Vec<CirclePointIndex>; 2],
    xs: &Vec<CirclePointIndex>,
) -> Vec<BaseField> {
    let mut x_polys: Vec<[Vec<BaseField>; 2]> = vec![];

    // TODO: to check correctness or possibly simplier this function
    for l in 0..=1 {
        for k in 0..folded_len {
            let interp_vals: Vec<BaseField> = (0..folding_param)
                .map(|j| vals[k + folded_len * j + eval_size * l])
                .collect();
            // TODO: proper error handling instead of using 'unwrap'

            let inpl = circ_lagrange_interp(
                &xs2s[l].iter().map(|x| x.to_point()).collect(),
                &interp_vals,
                true,
            )
            .unwrap();

            x_polys.push(inpl);
        }
    }

    let mut g_hat = vec![];
    for l in 0..=1 {
        for k in 0..folded_len {
            let polys = &x_polys[k + folded_len * l];
            let point = r_fold.mul_circle_point(xs[k + eval_size * l].to_point().conjugate());

            let eval = eval_circ_poly_at(&polys, &point);
            g_hat.push(eval);
        }
    }

    g_hat
}

fn shift_g_hat<B: BackendForChannel<MC>, MC: MerkleChannel>(
    g_hat: &Vec<BaseField>,
    coset: Coset,
    expand_factor: usize,
    p_offset: CirclePointIndex,
    eval_offset: CirclePointIndex,
) -> CircleEvaluation<B, BaseField, NaturalOrder> {
    let poly = interpolate::<B, MC>(
        &coset.repeated_double(expand_factor.ilog2()),
        p_offset,
        g_hat,
    );
    let shifted_domain = CircleDomain::new(coset.shift(eval_offset));
    let g_hat_shift = poly.evaluate(shifted_domain).bit_reverse();

    g_hat_shift
}

fn generate_rnd_t_values<MC: MerkleChannel>(
    channel: &mut MC::C,
    folded_len: usize,
    repetition_param: usize,
) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let mut t_vals = vec![];
    for _ in 0..repetition_param {
        let t_vals_bytes = channel.draw_random_bytes();
        let t_vals_bytes = [
            t_vals_bytes[0],
            t_vals_bytes[1],
            t_vals_bytes[2],
            t_vals_bytes[3],
        ];
        let t_val = u32::from_be_bytes(t_vals_bytes) % ((2 * folded_len) as u32);
        t_vals.push(t_val);

        channel.mix_u64(t_val as u64);
    }

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
    let r_comb = M31_CIRCLE_GEN.mul(rnds[0].0 .0 .0.into());

    // mix again to get randomness of the next value
    channel.mix_felts(&rnds);
    let (t_vals, t_shifts, t_conj) =
        generate_rnd_t_values::<MC>(channel, folded_len, repetition_param);

    (r_fold, r_comb, t_vals, t_shifts, t_conj)
}

fn interpolate<B: BackendForChannel<MC>, MC: MerkleChannel>(
    coset: &Coset,
    to_shift: CirclePointIndex,
    eval: &Vec<BaseField>,
) -> CirclePoly<B> {
    let domain = CircleDomain::new(coset.shift(to_shift));
    let evaluation = CircleEvaluation::<B, BaseField, NaturalOrder>::new(
        domain,
        eval.iter().map(|x| *x).collect(),
    );
    let poly = evaluation.clone().bit_reverse().interpolate();

    poly
}

fn get_betas<B: BackendForChannel<MC>, MC: MerkleChannel>(
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

fn calculate_rs_and_g_rs(
    r_outs: &Vec<CirclePoint<SecureField>>,
    betas: &Vec<SecureField>,
    t_shifts: &Vec<u32>,
    t_conj: &Vec<u32>,
    coset: &Coset,
    p_offset: CirclePointIndex,
    g_hat: &Vec<BaseField>,
    folded_len: usize,
) -> (Vec<CirclePoint<SecureField>>, Vec<SecureField>) {
    let mut rs = r_outs.to_vec();
    let mut g_rs = betas.to_vec();

    for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
        let rt2_exp = coset.repeated_double(t.ilog2());
        let mut intr: CirclePointIndex = p_offset + rt2_exp.initial_index;
        if k % 2 != 0 {
            intr = intr.conj();
        }
        rs.push(intr.to_secure_field_point());

        let g_value = g_hat[(*t as usize) + (*k as usize) * folded_len];
        g_rs.push(SecureField::from_m31(
            g_value,
            BaseField::zero(),
            BaseField::zero(),
            BaseField::zero(),
        ))
    }

    (rs, g_rs)
}

fn fold_val(
    rs: &Vec<CirclePoint<SecureField>>,
    g_rs: &Vec<SecureField>,
    xs: &Vec<CirclePointIndex>,
    eval_size: usize,
    r_comb: CirclePoint<BaseField>,
    g_hat_shift: &Vec<M31>,
) -> Vec<BaseField> {
    let pol = circ_lagrange_interp(&rs, &g_rs, false).unwrap();
    let pol_vals: Vec<BaseField> = xs
        .iter()
        .map(|x| eval_circ_poly_at(&pol, &x.to_point()))
        .collect();
    let zpol = circ_zpoly(&rs, None, true); // TODO: use `split_exts` to convert zpol to M31
    let zpol = circ_poly_to_int_poly(&zpol).unwrap();

    let mut vals = vec![];
    for j in 0..2 * eval_size {
        let zzz: M31 = g_hat_shift.at(j);
        let aaa = pol_vals[j];
        let denom = eval_circ_poly_at(&zpol, &xs[j].to_point());
        let a = (zzz - aaa) / denom;

        let geom_sum_res = geom_sum((xs[j].to_point() + r_comb).x, rs.len()); // yyyy is M31
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
    merkle_tree_val: &<B as ColumnOps<M31>>::Column,
    merkle_tree: &MerkleProver<B, MC::H>,
) -> MerkleDecommitment<<MC as MerkleChannel>::H> {
    let mut queried_index = vec![];
    for j in 0..folding_param {
        for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
            let index = (*t as usize) + (j * folded_len) + ((*k as usize) * eval_size);
            queried_index.push(index);
        }
    }

    let mut queries = BTreeMap::<u32, Vec<usize>>::new();
    queries.insert(merkle_tree_val.len().ilog2(), queried_index);

    let (_values, decommitment) = merkle_tree.decommit(queries.clone(), vec![merkle_tree_val]);

    decommitment
}

pub fn prove_low_degree<B: BackendForChannel<MC>, MC: MerkleChannel>(
    channel: &mut MC::C,
    mut coset: Coset,
    eval_sizes: Vec<usize>,
    repetition_params: Vec<usize>,
    folding_params: Vec<usize>,
    values: &Vec<BaseField>,
    eval_offsets: &Vec<CirclePointIndex>,
) -> Result<(), String> {
    let ood_rep = 1;
    let mut output_roots = vec![];
    let mut all_betas = vec![];
    let mut output_branches = vec![];

    let mut xs = calculate_xs(&coset, eval_offsets[0]);

    if values.len() != xs.len() && xs.len() / 2 != eval_sizes[0] {
        return Err("values.len() != xs.len() && xs.len()/2 != eval_sizes[0]".to_owned());
    }

    let mut vals = values.to_owned();
    // TODO: to check if this is correct
    let mut merkle_tree_val = vals.iter().map(|x| *x).collect();
    let mut merkle_tree: MerkleProver<B, MC::H> = MerkleProver::commit(vec![&merkle_tree_val]);
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

        let xs2s = calculate_xs2s(coset2, folding_params[i]);

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
        coset2 = coset2.repeated_double(expand_factor.ilog2());
        let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

        let g_hat_shift =
            shift_g_hat::<B, MC>(&g_hat, coset, expand_factor, p_offset, eval_offsets[i]);

        let m2: MerkleProver<B, MC::H> = MerkleProver::commit(vec![&g_hat_shift.values]);
        output_roots.push(m2.root());

        MC::mix_root(channel, merkle_tree.root());

        xs = calculate_xs(&coset, eval_offsets[i]);

        let r_outs: Vec<CirclePoint<SecureField>> = channel
            .draw_felts(ood_rep)
            .iter()
            .map(|v| (*v).into())
            .collect();

        let mut betas = get_betas::<B, MC>(&coset2, p_offset, &g_hat, &r_outs);

        channel.mix_felts(&betas);
        all_betas.append(&mut betas);

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

        let decommitment = open_merkle_tree(
            folding_params[i - 1],
            &t_shifts,
            &t_conj,
            folded_len,
            eval_sizes[i - 1],
            &merkle_tree_val,
            &merkle_tree,
        );
        output_branches.push(decommitment);

        merkle_tree_val = g_hat_shift.clone().values;
        merkle_tree = m2;

        vals = fold_val(
            &rs,
            &g_rs,
            &xs,
            eval_sizes[i],
            r_comb,
            &g_hat_shift.values.to_cpu(),
        );
    }

    let final_folding_param = folding_params[folding_params.len() - 1];
    let to_shift = eval_offsets[eval_offsets.len() - 1] * final_folding_param;
    let g_pol = interpolate::<B, MC>(
        &coset.repeated_double(final_folding_param as u32),
        to_shift,
        &g_hat,
    );

    let numer = values.len(); // maxdeg_plus_1
    let denom: usize = folding_params.iter().product();
    let final_deg = numer / denom;

    let g_pol_coeffs: Vec<BaseField> = g_pol.coeffs.to_cpu();
    let (_, g_pol_final) = g_pol_coeffs.split_at(2 * final_deg + 1);

    let is_zero = g_pol_final.iter().all(|x| *x == BaseField::zero());
    if is_zero {
        return Err("g_pol_final is zero. something is not right".to_string());
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

    let decommitment = open_merkle_tree(
        folding_params[folding_params.len() - 1],
        &t_shifts,
        &t_conj,
        folded_len,
        eval_sizes[folding_params.len() - 1],
        &merkle_tree_val,
        &merkle_tree,
    );

    output_branches.push(decommitment);

    Ok(())
}

fn geom_sum<F: Field>(x: F, p: usize) -> F {
    let mut ans = F::one();
    let mut prod = F::one();

    for _ in 0..p {
        prod = prod * x;
        ans = ans + prod;
    }

    ans
}

fn circ_zpoly<F>(
    pts: &Vec<CirclePoint<F>>,
    nzero: Option<CirclePoint<F>>,
    split_exts: bool,
) -> [Vec<F>; 2]
where
    F: Field + ToBaseField,
    CirclePoint<F>: AllConjugate,
{
    let mut pts = pts.clone();
    if split_exts {
        let mut pts2 = vec![];

        for p in pts {
            let mut all_conjs = p.all_conj();
            pts2.append(&mut all_conjs);
        }

        pts = pts2;
    }

    let mut ans: [Vec<F>; 2] = [vec![F::one()], vec![]];
    for i in 0..(pts.len() / 2) {
        ans = mul_circ_polys(&ans, &line(pts[2 * i], pts[2 * i + 1]));
    }
    if pts.len() % 2 == 1 {
        // if nzero.is_some() &&
        let pt = pts[pts.len() - 1];
        if let Some(_pt) = nzero {
            ans = mul_circ_polys(&ans, &[vec![pts[pts.len() - 1].y], vec![-F::one()]]);
        } else {
            ans = mul_circ_polys(&ans, &[vec![pts[pts.len() - 1].x, -F::one()], vec![]]);
        }
    }

    ans
}

fn eval_circ_poly_at<F: Field>(polys: &[Vec<F>; 2], point: &CirclePoint<F>) -> F {
    eval_poly_at(&polys[0], &point.x) + eval_poly_at(&polys[1], &point.x) * point.y
}

// Evaluate a polynomial at a point
fn eval_poly_at<F: Field>(poly: &Vec<F>, pt: &F) -> F {
    let mut y = F::zero();
    let mut power_of_x = F::one();

    for coeff in poly.iter() {
        y += power_of_x * *coeff;
        power_of_x = power_of_x * *pt;
    }

    y
}

// question: how does this self.modulus - 1 get translated to a QM value? because QM is comprises of
// 4 M31 values
fn line<F: Field>(pt1: CirclePoint<F>, pt2: CirclePoint<F>) -> [Vec<F>; 2] {
    let dx = pt1.x - pt2.x;
    if dx.is_zero() {
        return [vec![pt1.x, -F::one()], vec![]]; // -F::one() equivalent to the baseField's P-1 F
                                                 // can be any extension of the basefield
    }

    let slope = (pt1.y - pt2.y) / dx;
    [vec![pt1.y - slope * pt1.x, slope], vec![-F::one()]]
}

fn mul_circ_polys<F: Field>(a: &[Vec<F>; 2], b: &[Vec<F>; 2]) -> [Vec<F>; 2] {
    let a1b1 = mul_polys(&a[1], &b[1]);

    let x = sub_polys(
        &add_polys(&mul_polys(&a[0], &b[0]), &a1b1),
        &vec![F::zero(), F::zero()]
            .into_iter()
            .chain(a1b1.into_iter())
            .collect(),
    );

    let y = add_polys(&mul_polys(&a[0], &b[1]), &mul_polys(&a[1], &b[0]));

    [x, y]
}

fn add_circ_polys<F: Field>(a: &[Vec<F>; 2], b: &[Vec<F>; 2]) -> [Vec<F>; 2] {
    [add_polys(&a[0], &b[0]), add_polys(&a[1], &b[1])]
}

fn sub_circ_polys<F: Field>(a: &[Vec<F>; 2], b: &[Vec<F>; 2]) -> [Vec<F>; 2] {
    [sub_polys(&a[0], &b[0]), sub_polys(&a[1], &b[1])]
}

fn mul_circ_by_const<F: Field>(a: &[Vec<F>; 2], c: &F) -> [Vec<F>; 2] {
    [mul_poly_by_const(&a[0], &c), mul_poly_by_const(&a[1], &c)]
}

fn mul_polys<F: Field>(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
    let mut o = vec![F::zero(); a.len() + b.len() - 1];
    for i in 0..a.len() {
        for j in 0..b.len() {
            o[i + j] += a[i] * b[j];
        }
    }

    o
}

fn add_polys<F: Field>(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
    let max_iter = max([a.len(), b.len()]).unwrap();
    let mut res = vec![];

    for i in 0..max_iter {
        let a_i = if i < a.len() { a[i] } else { F::zero() };
        let b_i = if i < b.len() { b[i] } else { F::zero() };
        res.push(a_i + b_i);
    }

    res
}

fn sub_polys<F: Field>(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
    let max_iter = max([a.len(), b.len()]).unwrap();
    let mut res = vec![];

    for i in 0..max_iter {
        let a_i = if i < a.len() { a[i] } else { F::zero() };
        let b_i = if i < b.len() { b[i] } else { F::zero() };
        res.push(a_i - b_i);
    }

    res
}

// mul_by_const
fn mul_poly_by_const<F: Field>(poly: &Vec<F>, constant: &F) -> Vec<F> {
    poly.iter().map(|coeff| *coeff * *constant).collect()
}

fn circ_lagrange_interp<F>(
    pts: &Vec<CirclePoint<F>>,
    vals: &Vec<F>,
    normalize: bool,
) -> Result<[Vec<BaseField>; 2], String>
where
    F: Field + AllConjugate + ToBaseField,
    CirclePoint<F>: AllConjugate,
{
    if pts.len() != vals.len() {
        return Err("Cannot interpolate".to_owned());
    }

    let mut n_pts = vec![];
    let mut n_vals = vec![];

    for i in 0..pts.len() {
        let mut p_conj = pts[i].all_conj();
        let mut v_conj = vals[i].all_conj();

        if p_conj.len() != v_conj.len() {
            return Err("Cannot interpolate".to_owned());
        }

        n_pts.append(&mut p_conj);
        n_vals.append(&mut v_conj);
    }
    let pts = n_pts;
    let vals = n_vals;

    let mut ans = [vec![], vec![]];
    for i in 0..pts.len() {
        let pts_removed = pts[..i]
            .iter()
            .chain(pts[i + 1..].iter())
            .cloned()
            .collect();
        let pol = circ_zpoly(&pts_removed, Some(pts[i]), false);
        let scale = vals[i] / eval_circ_poly_at(&pol, &pts[i]);
        ans = add_circ_polys(&ans, &mul_circ_by_const(&pol, &scale));
    }

    if normalize && pts.len() % 2 == 0 {
        let d = pts.len() / 2;
        let zpol = circ_zpoly(&pts, None, false);
        let coef_a = if ans[1].len() >= d {
            ans[1][d - 1]
        } else {
            F::zero()
        };
        let scale = coef_a / zpol[1][d - 1];
        ans = sub_circ_polys(&ans, &mul_circ_by_const(&zpol, &scale));
    }

    for i in 0..pts.len() {
        let eval = eval_circ_poly_at(&ans, &pts[i]);
        if eval != vals[i] {
            return Err("Cannot interoplate".to_owned());
        }
    }

    circ_poly_to_int_poly(&ans)
}

fn circ_poly_to_int_poly<F>(p: &[Vec<F>; 2]) -> Result<[Vec<BaseField>; 2], String>
where
    F: Field + ToBaseField,
{
    let mut p0 = vec![];
    let mut p1 = vec![];

    for f in &p[0] {
        let m = f.to_basefield();
        if m.is_err() {
            return Err(m.unwrap_err());
        }

        p0.push(m.unwrap());
    }

    for f in &p[1] {
        let m = f.to_basefield();
        if m.is_err() {
            return Err(m.unwrap_err());
        }

        p1.push(m.unwrap());
    }

    Ok([p0, p1])
}

trait ToBaseField {
    fn to_basefield(&self) -> Result<BaseField, String>;
}

impl ToBaseField for M31 {
    fn to_basefield(&self) -> Result<BaseField, String> {
        Ok(*self)
    }
}

impl ToBaseField for CM31 {
    fn to_basefield(&self) -> Result<BaseField, String> {
        let m31_array = [self.0, self.1];
        if m31_array[1] != BaseField::zero() {
            return Err("m31_array[1] != 0".to_owned());
        }

        Ok(m31_array[0])
    }
}

impl ToBaseField for QM31 {
    fn to_basefield(&self) -> Result<BaseField, String> {
        let m31_array = self.to_m31_array();
        if m31_array[1] != BaseField::zero()
            || m31_array[2] != BaseField::zero()
            || m31_array[3] != BaseField::zero()
        {
            return Err("m31_array[1,2,3] != 0".to_owned());
        }

        Ok(m31_array[0])
    }
}

trait Conj {
    fn conj(&self) -> Self;
}

impl Conj for CirclePointIndex {
    fn conj(&self) -> Self {
        let conj_index: u32 = P - (self.0) as u32;
        // Self((P - self.0).try_into().unwrap())
        Self(conj_index as usize)
    }
}

// TODO: probably refactor this into the ComplexConjugate trait
trait AllConjugate {
    fn all_conj(&self) -> Vec<Self>
    where
        Self: Sized;
}

impl AllConjugate for BaseField {
    fn all_conj(&self) -> Vec<Self> {
        vec![*self]
    }
}

impl AllConjugate for CM31 {
    fn all_conj(&self) -> Vec<Self> {
        vec![*self, self.complex_conjugate()]
    }
}

impl AllConjugate for QM31 {
    fn all_conj(&self) -> Vec<Self> {
        let mut conj = vec![*self, self.complex_conjugate()];
        let mut conj_2: Vec<QM31> = conj.iter().map(|c| c.pow(P.into())).collect();

        conj.append(&mut conj_2);
        conj
    }
}

impl AllConjugate for CirclePoint<BaseField> {
    fn all_conj(&self) -> Vec<Self> {
        return vec![*self];
    }
}

impl AllConjugate for CirclePoint<CM31> {
    fn all_conj(&self) -> Vec<Self> {
        let x = &self.x.all_conj();
        let y = &self.y.all_conj();

        x.iter()
            .zip(y.iter())
            .map(|(x, y)| CirclePoint { x: *x, y: *y })
            .collect()
    }
}

impl AllConjugate for CirclePoint<QM31> {
    fn all_conj(&self) -> Vec<Self> {
        let x = &self.x.all_conj();
        let y = &self.y.all_conj();

        x.iter()
            .zip(y.iter())
            .map(|(x, y)| CirclePoint { x: *x, y: *y })
            .collect()
    }
}

impl CirclePoint<BaseField> {
    fn mul_circle_point(self, rhs: CirclePoint<BaseField>) -> Self {
        Self {
            x: self.x * rhs.x - self.y * rhs.y,
            y: self.x * rhs.y + self.y * rhs.x,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{circ_lagrange_interp, line, AllConjugate};
    use crate::core::backend::CpuBackend;
    use crate::core::circle::{CirclePoint, CirclePointIndex};
    use crate::core::circle_fft::{
        add_circ_polys, add_polys, circ_zpoly, eval_circ_poly_at, eval_poly_at, mul_circ_by_const,
        mul_circ_polys, mul_polys, sub_circ_polys, sub_polys,
    };
    use crate::core::fields::cm31::CM31;
    use crate::core::fields::m31::{BaseField, M31};
    use crate::core::pcs::PcsConfig;
    use crate::core::poly::circle::{CanonicCoset, CircleDomain, CircleEvaluation};
    use crate::core::poly::NaturalOrder;

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
    fn test_cm31_all_conj() {
        // return [self,CM(self.a,-self.b,self.modulus)]
        let val = CM31::from_m31(BaseField::from(123), BaseField::from(321));
        let conjs = val.all_conj();

        assert_eq!(conjs.len(), 2);
        assert_eq!(conjs[0], val);
        assert_eq!(
            conjs[1],
            CM31::from_m31(BaseField::from(123), BaseField::from(-321))
        )
    }

    #[test]
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

    // base field
    // cm31
    // qm31

    // circlepoint(basefield)
    // circlepoint(cm31)
    // circlepoint(qm31)

    #[test]
    fn test_line() {
        let pt1 = CirclePointIndex(1).to_point();
        let pt2 = CirclePointIndex(2).to_point();

        let line_res = line(pt1, pt2);
        assert_eq!(
            line_res,
            [
                vec![M31(1464384553), M31(2049297282)],
                vec![M31(2147483646)]
            ]
        );
        println!("{:?}", line_res);
    }

    #[test]
    fn test_mul_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = mul_polys(&a, &b);
        assert_eq!(res, vec![M31(35), M31(82), M31(48)]);
    }

    #[test]
    fn test_add_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = add_polys(&a, &b);
        assert_eq!(res, vec![M31(12), M31(14)]);
    }

    #[test]
    fn test_sub_polys() {
        let a = vec![M31(5), M31(6)];
        let b = vec![M31(7), M31(8)];

        let res = sub_polys(&a, &b);
        assert_eq!(res, vec![M31(2147483645), M31(2147483645)]);
    }

    #[test]
    fn test_mul_circ_polys() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = [vec![M31(7), M31(8)], vec![M31(9), M31(10)]];

        let res = mul_circ_polys(&a, &b);
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

        let res = add_circ_polys(&a, &b);

        // [[12, 14], [16, 18]]
        assert_eq!(res, [vec![M31(12), M31(14)], vec![M31(16), M31(18)]]);
    }

    #[test]
    fn test_sub_circ_polys() {
        let a = [vec![M31(5), M31(6)], vec![M31(7), M31(8)]];
        let b = [vec![M31(7), M31(8)], vec![M31(9), M31(10)]];

        let res = sub_circ_polys(&a, &b);
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

        let res = mul_circ_by_const(&a, &b);
        assert_eq!(res, [vec![M31(35), M31(42)], vec![M31(49), M31(56)]]);
    }

    #[test]
    fn test_circ_zpoly() {
        let a = vec![
            CirclePointIndex(1).to_point(),
            CirclePointIndex(2).to_point(),
            CirclePointIndex(3).to_point(),
        ];
        let res = circ_zpoly(&a, None, false);
        assert_eq!(
            res,
            [
                vec![M31(1566776379), M31(277737251), M31(98186365)],
                vec![M31(2147483621), M31(1)]
            ]
        );
    }

    #[test]
    fn test_eval_poly_at() {
        let poly = vec![M31(1), M31(2), M31(3)];
        let pt = M31(2);
        let res = eval_poly_at(&poly, &pt);
        assert_eq!(res, M31(17));
    }

    #[test]
    fn test_eval_circ_poly_at() {
        let poly = [vec![M31(1), M31(2), M31(3)], vec![M31(4), M31(5), M31(6)]];
        let pt = CirclePointIndex(1).to_point();
        let res = eval_circ_poly_at(&poly, &pt);
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
        .collect();
        println!("{:?}", pts);
        let values = vec![M31(1), M31(2), M31(3)];
        let res = circ_lagrange_interp(&pts, &values, false).unwrap();
        assert_eq!(res, [vec![M31(2), M31(2147483632)], vec![M31(463810318)]]);
    }

    #[test]
    fn test_fft_ifft_with_offset() {
        let poly_log_length = 4;
        let offset: CirclePointIndex = CirclePointIndex(2);
        let offset_point = offset.to_point();
        println!("{:?}", offset_point);
        let coset = CanonicCoset::new(poly_log_length).coset.shift(offset);
        let domain = CircleDomain::new(coset);
        let values: Vec<M31> = (0..1 << (poly_log_length + 1)).map(|x| M31(x)).collect();
        let evaluations =
            CircleEvaluation::<CpuBackend, BaseField, NaturalOrder>::new(domain, values.clone());
        let poly = evaluations.bit_reverse().interpolate();
        let coeffs = poly.clone().coeffs;
        assert_eq!(
            coeffs,
            [
                M31(1073741839),
                M31(0),
                M31(1498069892),
                M31(0),
                M31(269407359),
                M31(0),
                M31(2026037040),
                M31(0),
                M31(1915079382),
                M31(0),
                M31(34710855),
                M31(0),
                M31(958049463),
                M31(0),
                M31(2103180470),
                M31(0),
                M31(1218381196),
                M31(0),
                M31(1595441113),
                M31(0),
                M31(1167370379),
                M31(0),
                M31(1194789249),
                M31(0),
                M31(1348073476),
                M31(0),
                M31(1717137709),
                M31(0),
                M31(681422734),
                M31(0),
                M31(981687288),
                M31(1164983970)
            ]
        );

        let evals = poly.evaluate(domain).bit_reverse();
        assert_eq!(evals.values, values);
    }

    // circ_poly_to_int_poly

    #[test]
    fn test_g_hat() {
        todo!();
    }

    #[test]
    fn test_g_hat_shift() {
        todo!();
    }
}

// 1. test g_hat
// 2. test g_hat_shift
// 3. test beta from randomness
// 4. test circ_lagrange from r_s and g_s and eval_circ_poly_at with xs
// 5. test geo_sum and final val calculation
