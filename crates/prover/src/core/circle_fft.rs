#![allow(unused_variables)]
#![allow(unused_assignments)]

use std::collections::BTreeMap;

use itertools::max;
use num_traits::{One, Zero};

use super::backend::{BackendForChannel, Column};
use super::channel::{Channel, MerkleChannel};
use super::circle::{CirclePoint, CirclePointIndex, Coset, M31_CIRCLE_GEN};
use super::fields::cm31::CM31;
use super::fields::m31::{BaseField, M31, P};
use super::fields::qm31::{SecureField, QM31};
use super::fields::FieldExpOps;
use super::poly::circle::{CircleDomain, CircleEvaluation};
use super::poly::BitReversedOrder;
use super::vcs::prover::MerkleProver;

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

    let mut xs = coset.get_mul_cycle(eval_offsets[0]);
    // TODO: can we refactor this step of getting the conjugates? maybe somehow using `conjugate`
    // function?
    let mut xs_conj: Vec<CirclePointIndex> = xs.iter().map(|x| x.conj()).collect();
    xs.append(&mut xs_conj);

    if values.len() != xs.len() && xs.len() / 2 != eval_sizes[0] {
        return Err("values.len() != xs.len() && xs.len()/2 != eval_sizes[0]".to_owned());
    }

    let vals = values.to_owned();
    // TODO: to check if this is correct
    // TODO: always combine commit with mix_root?
    let mut merkle_tree_val_log_size = vals.len().ilog2();
    let mut merkle_tree_val = vals.iter().map(|x| *x).collect();
    let mut merkle_tree: MerkleProver<B, MC::H> = MerkleProver::commit(vec![&merkle_tree_val]);
    output_roots.push(merkle_tree.root());

    MC::mix_root(channel, merkle_tree.root());

    // TODO: not correct as we are not surd that the x and y are indeed on the circle
    // primitive root for M31 Gaussian(311014874, 1584694829)
    // CirclePoint mul by M31 value
    let rnd = channel.draw_felt();
    let mut r_fold = M31_CIRCLE_GEN.mul(rnd.0 .0 .0.into());

    for i in 1..folding_params.len() + 1 {
        // # fold using r-fold
        if eval_sizes[i - 1] % folding_params[i - 1] != 0 {
            return Err("eval_sizes[i-1] % folding_params[i-1] != 0".to_owned());
        }

        let folded_len = eval_sizes[i - 1] / folding_params[i - 1];
        let mut coset2 = coset.repeated_double(folded_len.ilog2());

        let mut xs2s: [Vec<CirclePointIndex>; 2] = [vec![], vec![]];
        xs2s[0] = coset2.get_mul_cycle(CirclePointIndex(1));
        xs2s[1] = (0..folding_params[i])
            .map(|j| xs2s[0][xs2s[0].len() - j - 1])
            .collect();

        let mut x_polys: Vec<[Vec<BaseField>; 2]> = vec![];

        // TODO: to check correctness or possibly simplier this function
        for l in 0..=1 {
            for k in 0..folded_len {
                let interp_vals: Vec<BaseField> = (0..folding_params[i - 1])
                    .map(|j| vals[k + folded_len * j + eval_sizes[i - 1] * l])
                    .collect();
                // TODO: proper error handling instead of using 'unwrap'
                let inpl = circ_lagrange_interp(&xs2s[l], &interp_vals, true).unwrap();
                x_polys.push(inpl);
            }
        }

        let mut g_hat = vec![];
        for l in 0..=1 {
            for k in 0..folded_len {
                let polys = &x_polys[k + folded_len * l];
                let point =
                    r_fold.mul_circle_point(xs[k + eval_sizes[i - 1] * l].to_point().conjugate());

                let eval = eval_circ_poly_at(&polys, &point);
                g_hat.push(eval);
            }
        }

        if i == folding_params.len() {
            break;
        }

        if eval_sizes[i] % folded_len != 0 {
            return Err("eval_sizes[i] % folded_len != 0".into());
        }

        let expand_factor = eval_sizes[i] / folded_len;

        if eval_sizes[i - 1] % eval_sizes[i] != 0 {
            return Err("self.eval_sizes[i-1] % self.eval_sizes[i] != 0".into());
        }

        let eval_size_scale = eval_sizes[i - 1] / eval_sizes[i];
        coset = coset.repeated_double(eval_size_scale.ilog2());
        coset2 = coset2.repeated_double(expand_factor.ilog2());

        let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

        let g_hat_domain =
            CircleDomain::new(coset.repeated_double(expand_factor.ilog2())).shift(p_offset);
        let g_hat_evaluate = CircleEvaluation::<B, BaseField, BitReversedOrder>::new(
            g_hat_domain,
            g_hat.iter().map(|x| *x).collect(),
        );

        let poly = g_hat_evaluate.clone().interpolate();
        let shifted_domain = CircleDomain::new(coset.shift(eval_offsets[i]));
        let g_hat_shift = poly.evaluate(shifted_domain);

        let m2: MerkleProver<B, MC::H> = MerkleProver::commit(vec![&g_hat_shift.values]);
        output_roots.push(m2.root());

        MC::mix_root(channel, merkle_tree.root());

        xs = coset.get_mul_cycle(eval_offsets[i]);
        let mut xs_conj: Vec<CirclePointIndex> = xs.iter().map(|x| x.conj()).collect();
        xs.append(&mut xs_conj);

        let r_outs = channel.draw_felts(ood_rep);

        let inv_fft_domain = CircleDomain::new(coset2.shift(p_offset));
        let g_hat_evaluate = CircleEvaluation::<B, BaseField, BitReversedOrder>::new(
            inv_fft_domain,
            g_hat.iter().map(|x| *x).collect(),
        );
        let poly = g_hat_evaluate.clone().interpolate();

        // TODO: to check correctness of this betas result
        let mut betas: Vec<SecureField> = r_outs
            .iter()
            .map(|o| poly.eval_at_point((*o).into()))
            .collect();

        channel.mix_felts(&betas);
        all_betas.append(&mut betas);

        let rnds = channel.draw_felts(2);
        r_fold = M31_CIRCLE_GEN.mul(rnds[0].0 .0 .0.into());
        let r_comb = M31_CIRCLE_GEN.mul(rnds[0].0 .0 .0.into());

        // mix again to get randomness of the next value
        channel.mix_felts(&rnds);
        let t_vals_bytes = channel.draw_random_bytes();
        let t_vals_bytes = [
            t_vals_bytes[0],
            t_vals_bytes[1],
            t_vals_bytes[2],
            t_vals_bytes[3],
        ];

        let t_vals = u32::from_be_bytes(t_vals_bytes) % ((2 * folded_len) as u32);
        let t_shifts: Vec<u32> = (0..t_vals).map(|t| t / 2).collect();
        let t_conj: Vec<u32> = (0..t_vals).map(|t| t % 2).collect();

        if repetition_params[i - 1] % 2 != 0 {
            return Err("self.repetition_params[i-1]%2 != 0".to_owned());
        }

        // rs = r_outs + [f.mul(p_offset,f.exp(rt2,t)).conj(k)%self.modulus for (t,k) in
        // zip(t_shifts,t_conj)]
        let mut rs = r_outs;
        for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
            let rt2_exp = coset2.repeated_double(t.ilog2());
            let intr: CirclePointIndex = p_offset + rt2_exp.initial_index;
            // can convert intr to QM31 using from_m31 (with b,c,d be zero)

            // TODO: apply conj(k)
            // question: this is CirclePointIndex, how do i convert this to QM31?
            // rs.push(intr);
        }

        // g_rs = betas + [g_hat[t + k*folded_len] for (t,k) in zip(t_shifts,t_conj)]
        // TODO: rs and g_rs can be combined
        let mut g_rs = betas;
        for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
            // question: same issue here, betas are in QM31 and g_hat is in BaseField
            // g_rs.push(g_hat[(*t as usize) + (*k as usize) * folded_len]);
        }

        let mut queried_index = vec![];
        for j in 0..folding_params[i - 1] {
            for (t, k) in t_shifts.iter().zip(t_conj.iter()) {
                let index = (*t as usize) + (j * folded_len) + ((*k as usize) * eval_sizes[i - 1]);
                queried_index.push(index);
            }
        }

        let mut queries = BTreeMap::<u32, Vec<usize>>::new();
        queries.insert(merkle_tree_val_log_size, queried_index);

        let (_values, decommitment) = merkle_tree.decommit(queries.clone(), vec![&merkle_tree_val]);
        output_branches.push(decommitment);

        // m = m2
        // TODO: merkle_tree_val_log_size can be removed by getting length from merkle_tree_val
        merkle_tree_val_log_size = g_hat_shift.values.len().ilog2();
        merkle_tree_val = g_hat_shift.values;
        merkle_tree = m2;

        // Question: how do we lagrange interpolate QM31?? 
        // pol = f.circ_lagrange_interp(rs,g_rs)
        // pol_vals = [f.eval_circ_poly_at(pol,x) for x in xs]
        // zpol = f.circ_zpoly(rs)
    }

    Ok(())
}

fn circ_zpoly<const MOD: u32>(
    pts: &Vec<CirclePoint<BaseField>>,
    nzero: Option<CirclePoint<BaseField>>,
) -> [Vec<M31>; 2] {
    let mut ans = [vec![M31(1)], vec![M31(0)]];
    for i in 0..(pts.len() / 2) {
        ans = mul_circ_polys(&ans, &line::<MOD>(pts[2 * i], pts[2 * i + 1]));
    }
    if pts.len() % 2 == 1 {
        // if nzero.is_some() &&
        let pt = pts[pts.len() - 1];
        if let Some(_pt) = nzero {
            ans = mul_circ_polys(&ans, &[vec![pts[pts.len() - 1].y], vec![M31(MOD - 1)]]);
        } else {
            ans = mul_circ_polys(&ans, &[vec![pts[pts.len() - 1].x, M31(MOD - 1)], vec![]]);
        }
    }

    ans
}


// TODO: to support for both BaseField and SecureField
fn eval_circ_poly_at(polys: &[Vec<M31>; 2], point: &CirclePoint<BaseField>) -> BaseField {
    eval_poly_at(&polys[0], &point.x) + eval_poly_at(&polys[1], &point.x) * point.y
}

// Evaluate a polynomial at a point
fn eval_poly_at(poly: &Vec<M31>, pt: &BaseField) -> BaseField {
    let mut y = BaseField::zero();
    let mut power_of_x = BaseField::one();

    for coeff in poly.iter() {
        y += power_of_x * *coeff;
        power_of_x = power_of_x * *pt;
    }

    y
}

fn line<const MOD: u32>(pt1: CirclePoint<BaseField>, pt2: CirclePoint<BaseField>) -> [Vec<M31>; 2] {
    let dx = pt1.x - pt2.x;
    if dx.is_zero() {
        return [vec![pt1.x, M31(MOD - 1)], vec![]];
    }

    let slope = (pt1.y - pt2.y) / dx;
    [vec![pt1.y - slope * pt1.x, slope], vec![M31(MOD - 1)]]
}

fn mul_circ_polys(a: &[Vec<BaseField>; 2], b: &[Vec<BaseField>; 2]) -> [Vec<M31>; 2] {
    let a1b1 = mul_polys(&a[1], &b[1]);

    let x = sub_polys(
        &add_polys(&mul_polys(&a[0], &b[0]), &a1b1),
        &vec![M31(0), M31(0)]
            .into_iter()
            .chain(a1b1.into_iter())
            .collect(),
    );

    let y = add_polys(&mul_polys(&a[0], &b[1]), &mul_polys(&a[1], &b[0]));

    [x, y]
}

fn add_circ_polys(a: &[Vec<BaseField>; 2], b: &[Vec<BaseField>; 2]) -> [Vec<BaseField>; 2] {
    [add_polys(&a[0], &b[0]), add_polys(&a[1], &b[1])]
}

fn sub_circ_polys(a: &[Vec<BaseField>; 2], b: &[Vec<BaseField>; 2]) -> [Vec<BaseField>; 2] {
    [sub_polys(&a[0], &b[0]), sub_polys(&a[1], &b[1])]
}

fn mul_circ_by_const(a: &[Vec<BaseField>; 2], c: &BaseField) -> [Vec<BaseField>; 2] {
    [mul_poly_by_const(&a[0], &c), mul_poly_by_const(&a[1], &c)]
}

fn mul_polys(a: &Vec<BaseField>, b: &Vec<BaseField>) -> Vec<BaseField> {
    let mut o = vec![M31(0); a.len() + b.len() - 1];
    for i in 0..a.len() {
        for j in 0..b.len() {
            o[i + j] += a[i] * b[j];
        }
    }

    o
}

fn add_polys(a: &Vec<BaseField>, b: &Vec<BaseField>) -> Vec<BaseField> {
    let max_iter = max([a.len(), b.len()]).unwrap();
    let mut res = vec![];

    for i in 0..max_iter {
        let a_i = if i < a.len() { a[i] } else { M31(0) };
        let b_i = if i < b.len() { b[i] } else { M31(0) };
        res.push(a_i + b_i);
    }

    res
}

fn sub_polys(a: &Vec<BaseField>, b: &Vec<BaseField>) -> Vec<BaseField> {
    let max_iter = max([a.len(), b.len()]).unwrap();
    let mut res = vec![];

    for i in 0..max_iter {
        let a_i = if i < a.len() { a[i] } else { M31(0) };
        let b_i = if i < b.len() { b[i] } else { M31(0) };
        res.push(a_i - b_i);
    }

    res
}

// mul_by_const
fn mul_poly_by_const(poly: &Vec<BaseField>, constant: &BaseField) -> Vec<BaseField> {
    poly.iter().map(|coeff| *coeff * *constant).collect()
}

// TODO: to refactor to support for both BaseField and SecureField
fn circ_lagrange_interp(
    pts: &Vec<CirclePointIndex>,
    vals: &Vec<BaseField>,
    normalize: bool,
) -> Result<[Vec<M31>; 2], String> {
    if pts.len() != vals.len() {
        return Err("Cannot interpolate".to_owned());
    }

    let mut n_pts = vec![];
    let mut n_vals = vec![];

    for i in 0..pts.len() {
        let mut p_conj = pts[i].to_point().all_conj();
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
        let pol = circ_zpoly::<P>(&pts_removed, Some(pts[i]));
        let scale = vals[i] / eval_circ_poly_at(&pol, &pts[i]);
        ans = add_circ_polys(&ans, &mul_circ_by_const(&pol, &scale));
    }

    if normalize && pts.len() % 2 == 0 {
        let d = pts.len() / 2;
        let zpol = circ_zpoly::<P>(&pts, None);
        let coef_a = if ans[1].len() >= d {
            ans[1][d - 1]
        } else {
            BaseField::zero()
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

    Ok(ans)
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

trait Conjugate<T> {
    fn all_conj(&self) -> Vec<T>;
}

impl Conjugate<BaseField> for BaseField {
    fn all_conj(&self) -> Vec<BaseField> {
        vec![*self]
    }
}

impl Conjugate<CM31> for CM31 {
    fn all_conj(&self) -> Vec<CM31> {
        vec![*self, CM31(self.0, -self.1)]
    }
}

impl Conjugate<QM31> for QM31 {
    fn all_conj(&self) -> Vec<QM31> {
        // todo!()

        let mut conj = vec![*self, QM31(self.0, -self.1)];
        let mut conj_2: Vec<QM31> = conj.iter().map(|c| c.pow(P.into())).collect();

        conj.append(&mut conj_2);
        conj
    }
}

impl Conjugate<CirclePoint<BaseField>> for CirclePoint<BaseField> {
    fn all_conj(&self) -> Vec<CirclePoint<BaseField>> {
        return vec![*self];
    }
}

impl Conjugate<CirclePoint<CM31>> for CirclePoint<CM31> {
    fn all_conj(&self) -> Vec<CirclePoint<CM31>> {
        let x = &self.x.all_conj();
        let y = &self.y.all_conj();

        x.iter()
            .zip(y.iter())
            .map(|(x, y)| CirclePoint { x: *x, y: *y })
            .collect()
    }
}

impl Conjugate<CirclePoint<QM31>> for CirclePoint<QM31> {
    fn all_conj(&self) -> Vec<CirclePoint<QM31>> {
        let x = &self.x.all_conj();
        let y = &self.y.all_conj();

        x.iter()
            .zip(y.iter())
            .map(|(x, y)| CirclePoint { x: *x, y: *y })
            .collect()
    }
}

// impl Mul<CirclePoint<BaseField>> for CirclePoint<BaseField> {
//     type Output = Self;

//     fn mul(self, rhs: CirclePoint<BaseField>) -> Self::Output {
//         Self::Output {
//             x: self.x * rhs.x - self.y * rhs.y,
//             y: self.x * rhs.y + self.y * rhs.x,
//         }
//     }
// }

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
    use super::Conjugate;
    use crate::core::circle::CirclePointIndex;
    use crate::core::fields::cm31::CM31;
    use crate::core::fields::m31::BaseField;
    use crate::core::pcs::PcsConfig;
    use crate::core::poly::circle::CanonicCoset;

    #[test]
    fn test_get_mul_cycle() {
        const LOG_N_INSTANCES: u32 = 6;
        let config = PcsConfig::default();
        let coset = CanonicCoset::new(LOG_N_INSTANCES + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset;

        let xs = coset.get_mul_cycle(CirclePointIndex(1));
        println!("{:?}", xs);
    }

    // def all_conj(p):
    //     if isinstance(p,Gaussian):
    //         if isinstance(p.x,int):
    //             return [p]
    //         else:
    //             return [Gaussian(x,y) for x,y in zip(p.x.all_conj(),p.y.all_conj())]
    //     else:
    //         if isinstance(p,int):
    //             return [p]
    //         else:
    //             return p.all_conj()

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
}
