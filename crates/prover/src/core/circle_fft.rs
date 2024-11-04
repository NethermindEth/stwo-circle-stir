// # fold using r-fold
//             assert self.eval_sizes[i-1] % self.folding_params[i-1] == 0
//             folded_len = self.eval_sizes[i-1]//self.folding_params[i-1]
//             #should replace lagrange_interp with an fft?
//             rt2 = f.exp(rt, folded_len)
//             xs2s = [get_power_cycle(rt2, self.modulus, Gaussian(1,0))]
//             xs2s.append([xs2s[0][-j] for j in range(self.folding_params[i-1])]) # chee: what does
// this mean?             x_polys =\
//                 [f.circ_lagrange_interp(xs2s[l], #chee: interpolate at xs2s points for vals
//                                         [vals[k + folded_len*j + self.eval_sizes[i-1]*l] for j in
// range(self.folding_params[i-1])],                                         normalize=True) for l
// in [0,1] for k in range(folded_len)] #chee: i dont really get this, why is there an array in an
// array?             g_hat = [f.eval_circ_poly_at(x_polys[k + folded_len*l],
//                                          f.mul(r_fold, xs[k + self.eval_sizes[i-1]*l].conj()))
// for l in [0,1] for k in range(folded_len)]

//             if i == len(self.folding_params):
//                 break
#![allow(unused_variables)]
#![allow(unused_assignments)]

use itertools::max;
use num_traits::{One, Zero};

use super::circle::{CirclePoint, CirclePointIndex, Coset};
use super::fields::cm31::CM31;
use super::fields::m31::{BaseField, M31, P};
use super::fields::qm31::QM31;
use super::fields::FieldExpOps;

const MOD: u32 = P;

pub fn circle_to_circle_fold(
    coset: Coset,
    eval_sizes: Vec<usize>,
    folding_params: Vec<usize>,
    values: &Vec<BaseField>,
    r_fold: &CirclePoint<BaseField>,
    eval_offsets: &Vec<CirclePointIndex>,
) -> Result<(), String> {
    let mut root_of_unity = coset.initial_index * coset.step_size.0;

    let mut xs: Vec<CirclePointIndex> = get_mul_cycle::<MOD>(root_of_unity, eval_offsets[0]);
    let mut xs_conj: Vec<CirclePointIndex> = xs.iter().map(|x| x.conj()).collect();
    xs.append(&mut xs_conj);

    let vals = values.to_owned();

    // TODO: check consistency of index i
    for i in 0..folding_params.len() {
        if eval_sizes[i] % folding_params[i] != 0 {
            return Err("eval_sizes % folding_params != 0".into());
        }

        let folded_len = eval_sizes[i] / folding_params[i];
        let mut root_of_unity_2 = root_of_unity * folded_len;

        let mut xs2s = vec![get_mul_cycle::<MOD>(root_of_unity_2, CirclePointIndex(1))];
        xs2s.push(
            (0..folding_params[i])
                .map(|j| xs2s[0][xs2s[0].len() - j - 1])
                .collect(),
        );

        let mut x_polys: Vec<Vec<Vec<BaseField>>> = vec![];
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
                let point = (*r_fold)
                    .mul_circle_point(xs[k + eval_sizes[i - 1] * l].to_point().conjugate());

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

        root_of_unity = root_of_unity * eval_size_scale;
        root_of_unity_2 = root_of_unity * expand_factor;
        let p_offset = eval_offsets[i - 1] * folding_params[i - 1];

        // # chee: what are these rt and rt2 for?
        // g_hat_shift = shift_domain(g_hat, self.modulus, rt, p_offset, self.eval_offsets[i],
        // expand = expand_factor) m2 = merkelize(g_hat_shift) // to use  MerkleProver::commit
        // output += m2[1]

        // xs = get_power_cycle(rt, self.modulus, self.eval_offsets[i])
        // xs += [x.conj()%self.modulus for x in xs]

        xs = get_mul_cycle::<MOD>(root_of_unity, eval_offsets[i]);
        let mut xs_conj: Vec<CirclePointIndex> = xs.iter().map(|x| x.conj()).collect();
        xs.append(&mut xs_conj);
    }

    Ok(())
}

// MOD:usize will not be needed here if the addition aldy handles modulus internally
fn get_mul_cycle<const MOD: u32>(
    root_of_unity: CirclePointIndex,
    offset: CirclePointIndex,
) -> Vec<CirclePointIndex> {
    let mut os = vec![offset];

    loop {
        // the modulus should have been covered here?
        let o: CirclePointIndex = os.last().unwrap().to_owned() + root_of_unity;
        os.push(o);

        if o == offset {
            break;
        }
    }

    os.reverse();
    os
}

fn circ_zpoly<const MOD: u32>(
    pts: &Vec<CirclePoint<BaseField>>,
    nzero: Option<CirclePoint<BaseField>>,
) -> Vec<Vec<M31>> {
    let mut ans = vec![vec![M31(1)], vec![M31(0)]];
    for i in 0..(pts.len() / 2) {
        ans = mul_circ_polys(&ans, &line::<MOD>(pts[2 * i], pts[2 * i + 1]));
    }
    if pts.len() % 2 == 1 {
        // if nzero.is_some() &&
        let pt = pts[pts.len() - 1];
        if let Some(_pt) = nzero {
            ans = mul_circ_polys(&ans, &vec![vec![pts[pts.len() - 1].y], vec![M31(MOD - 1)]]);
        } else {
            ans = mul_circ_polys(
                &ans,
                &vec![vec![pts[pts.len() - 1].x, M31(MOD - 1)], vec![]],
            );
        }
    }

    // if split_exts:
    //         ans = circ_poly_to_int_poly(ans)

    ans
}

fn eval_circ_poly_at(polys: &Vec<Vec<M31>>, point: &CirclePoint<BaseField>) -> BaseField {
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

fn line<const MOD: u32>(pt1: CirclePoint<BaseField>, pt2: CirclePoint<BaseField>) -> Vec<Vec<M31>> {
    let dx = pt1.x - pt2.x;
    if dx.is_zero() {
        return vec![vec![pt1.x, M31(MOD - 1)], vec![]];
    }

    let slope = (pt1.y - pt2.y) / dx;
    vec![vec![pt1.y - slope * pt1.x, slope], vec![M31(MOD - 1)]]
}

fn mul_circ_polys(a: &Vec<Vec<BaseField>>, b: &Vec<Vec<BaseField>>) -> Vec<Vec<M31>> {
    let a1b1 = mul_polys(&a[1], &b[1]);

    let x = sub_polys(
        &add_polys(&mul_polys(&a[0], &b[0]), &a1b1),
        &vec![M31(0), M31(0)]
            .into_iter()
            .chain(a1b1.into_iter())
            .collect(),
    );

    let y = add_polys(&mul_polys(&a[0], &b[1]), &mul_polys(&a[1], &b[0]));

    vec![x, y]
}

fn add_circ_polys(a: &Vec<Vec<BaseField>>, b: &Vec<Vec<BaseField>>) -> Vec<Vec<BaseField>> {
    vec![add_polys(&a[0], &b[0]), add_polys(&a[1], &b[1])]
}

fn sub_circ_polys(a: &Vec<Vec<BaseField>>, b: &Vec<Vec<BaseField>>) -> Vec<Vec<BaseField>> {
    vec![sub_polys(&a[0], &b[0]), sub_polys(&a[1], &b[1])]
}

fn mul_circ_by_const(a: &Vec<Vec<BaseField>>, c: &BaseField) -> Vec<Vec<BaseField>> {
    vec![mul_poly_by_const(&a[0], &c), mul_poly_by_const(&a[1], &c)]
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

// TODO: use enums for error strings
fn circ_lagrange_interp(
    pts: &Vec<CirclePointIndex>,
    vals: &Vec<BaseField>,
    normalize: bool,
) -> Result<Vec<Vec<BaseField>>, String> {
    if pts.len() != vals.len() {
        return Err("Cannot interoplate".to_owned());
    }

    let mut n_pts = vec![];
    let mut n_vals = vec![];

    for i in 0..pts.len() - 1 {
        let mut p_conj = pts[i].to_point().all_conj();
        let mut v_conj = vals[i].all_conj();

        if p_conj.len() != v_conj.len() {
            return Err("Cannot interoplate".to_owned());
        }

        n_pts.append(&mut p_conj);
        n_vals.append(&mut v_conj);
    }

    let pts = n_pts;
    let vals = n_vals;

    let mut ans = vec![vec![], vec![]];
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
    // return circ_poly_to_int_poly(ans)

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
    use super::super::fields::m31::P;
    use super::get_mul_cycle;
    use crate::core::circle::CirclePointIndex;
    use crate::core::pcs::PcsConfig;
    use crate::core::poly::circle::CanonicCoset;

    #[test]
    fn test_get_mul_cycle() {
        const LOG_N_INSTANCES: u32 = 6;
        let config = PcsConfig::default();
        let coset = CanonicCoset::new(LOG_N_INSTANCES + 1 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset;

        let root_of_unity = coset.initial_index * coset.step_size.0;
        let xs = get_mul_cycle::<P>(root_of_unity, CirclePointIndex(1));
        println!("{:?}", xs);
    }
}
