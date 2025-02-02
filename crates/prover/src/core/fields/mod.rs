use std::fmt::{Debug, Display};
use std::iter::{Product, Sum};
use std::ops::{Mul, MulAssign, Neg};

use m31::M31;
use num_traits::{NumAssign, NumAssignOps, NumOps, One};

use super::backend::ColumnOps;
use super::circle::CirclePoint;

pub mod cm31;
pub mod m31;
pub mod qm31;
pub mod secure_column;

pub trait FieldOps<F: Field>: ColumnOps<F> {
    // TODO(Ohad): change to use a mutable slice.
    fn batch_inverse(column: &Self::Column, dst: &mut Self::Column);
}

pub trait FieldPolyOps {
    type Field: Field;

    fn mul_polys(&self, other: &Self) -> Self;
    fn add_polys(&self, other: &Self) -> Self;
    fn sub_polys(&self, other: &Self) -> Self;
    fn mul_poly_by_const(&self, constant: &Self::Field) -> Self;

    // Evaluate a polynomial at a point
    fn eval_poly_at(&self, pt: &Self::Field) -> Self::Field;
}

pub trait FieldCircPolyOps {
    type Field: Field;

    fn mul_circ_polys(&self, other: &Self) -> Self;
    fn add_circ_polys(&self, other: &Self) -> Self;
    fn sub_circ_polys(&self, other: &Self) -> Self;
    fn mul_circ_by_const(&self, constant: &Self::Field) -> Self;

    fn eval_circ_poly_at(&self, point: &CirclePoint<Self::Field>) -> Self::Field;
    fn circ_poly_to_int_poly(&self) -> Result<[Vec<M31>; 2], String>;
}

pub trait CircPolyInterpolation {
    type Field: Field + AllConjugate;

    fn circ_zpoly(
        &self,
        nzero: Option<CirclePoint<Self::Field>>,
        split_exts: bool,
        oods_rep: Option<usize>,
    ) -> [Vec<Self::Field>; 2];

    fn circ_lagrange_interp(
        &self,
        vals: &Vec<Self::Field>,
        normalize: bool,
    ) -> Result<[Vec<M31>; 2], String>
    where
        CirclePoint<Self::Field>: AllConjugate;

    // pub fn circ_lagrange_interp<F>(
    //     pts: &Vec<CirclePoint<F>>,
    //     vals: &Vec<F>,
    //     normalize: bool,
    // ) -> Result<[Vec<BaseField>; 2], String>
    // where
    //     F: Field + AllConjugate,
    //     CirclePoint<F>: AllConjugate,
    // {
    //     if pts.len() != vals.len() {
    //         return Err("Cannot interpolate".to_owned());
    //     }

    //     let mut n_pts = vec![];
    //     let mut n_vals = vec![];

    //     for i in 0..pts.len() {
    //         let mut p_conj = pts[i].all_conj();
    //         let mut v_conj = vals[i].all_conj();

    //         if p_conj.len() != v_conj.len() {
    //             return Err("Cannot interpolate".to_owned());
    //         }

    //         n_pts.append(&mut p_conj);
    //         n_vals.append(&mut v_conj);
    //     }
    //     let pts = n_pts;
    //     let vals = n_vals;

    //     let mut ans = [vec![], vec![]];
    //     for i in 0..pts.len() {
    //         let pts_removed = pts[..i]
    //             .iter()
    //             .chain(pts[i + 1..].iter())
    //             .cloned()
    //             .collect();

    //         let pol = circ_zpoly(&pts_removed, Some(pts[i]), false, None);
    //         let scale = vals[i] / eval_circ_poly_at(&pol, &pts[i]);
    //         ans = add_circ_polys(&ans, &mul_circ_by_const(&pol, &scale));
    //     }

    //     if normalize && pts.len() % 2 == 0 {
    //         let d = pts.len() / 2;
    //         let zpol = circ_zpoly(&pts, None, false, None);
    //         let coef_a = if ans[1].len() >= d {
    //             ans[1][d - 1]
    //         } else {
    //             F::zero()
    //         };
    //         let scale = coef_a / zpol[1][d - 1];
    //         ans = sub_circ_polys(&ans, &mul_circ_by_const(&zpol, &scale));
    //     }

    //     for i in 0..pts.len() {
    //         let eval = eval_circ_poly_at(&ans, &pts[i]);
    //         if eval != vals[i] {
    //             return Err("Cannot interoplate".to_owned());
    //         }
    //     }

    //     circ_poly_to_int_poly(&ans)
    // }
}

pub trait FieldExpOps: Mul<Output = Self> + MulAssign + Sized + One + Clone {
    fn square(&self) -> Self {
        self.clone() * self.clone()
    }

    fn pow(&self, exp: u128) -> Self {
        let mut res = Self::one();
        let mut base = self.clone();
        let mut exp = exp;
        while exp > 0 {
            if exp & 1 == 1 {
                res *= base.clone();
            }
            base = base.square();
            exp >>= 1;
        }
        res
    }

    fn inverse(&self) -> Self;

    /// Inverts a batch of elements using Montgomery's trick.
    fn batch_inverse(column: &[Self], dst: &mut [Self]) {
        const WIDTH: usize = 4;
        let n = column.len();
        debug_assert!(dst.len() >= n);

        if n <= WIDTH || n % WIDTH != 0 {
            batch_inverse_classic(column, dst);
            return;
        }

        // First pass. Compute 'WIDTH' cumulative products in an interleaving fashion, reducing
        // instruction dependency and allowing better pipelining.
        let mut cum_prod: [Self; WIDTH] = std::array::from_fn(|_| Self::one());
        dst[..WIDTH].clone_from_slice(&cum_prod);
        for i in 0..n {
            cum_prod[i % WIDTH] *= column[i].clone();
            dst[i] = cum_prod[i % WIDTH].clone();
        }

        // Inverse cumulative products.
        // Use classic batch inversion.
        let mut tail_inverses: [Self; WIDTH] = std::array::from_fn(|_| Self::one());
        batch_inverse_classic(&dst[n - WIDTH..], &mut tail_inverses);

        // Second pass.
        for i in (WIDTH..n).rev() {
            dst[i] = dst[i - WIDTH].clone() * tail_inverses[i % WIDTH].clone();
            tail_inverses[i % WIDTH] *= column[i].clone();
        }
        dst[0..WIDTH].clone_from_slice(&tail_inverses);
    }
}

/// Assumes dst is initialized and of the same length as column.
fn batch_inverse_classic<T: FieldExpOps>(column: &[T], dst: &mut [T]) {
    let n = column.len();
    debug_assert!(dst.len() >= n);

    dst[0] = column[0].clone();
    // First pass.
    for i in 1..n {
        dst[i] = dst[i - 1].clone() * column[i].clone();
    }

    // Inverse cumulative product.
    let mut curr_inverse = dst[n - 1].inverse();

    // Second pass.
    for i in (1..n).rev() {
        dst[i] = dst[i - 1].clone() * curr_inverse.clone();
        curr_inverse *= column[i].clone();
    }
    dst[0] = curr_inverse;
}

pub trait Field:
    NumAssign
    + Neg<Output = Self>
    + ComplexConjugate
    + Copy
    + Default
    + Debug
    + Display
    + PartialOrd
    + Ord
    + Send
    + Sync
    + Sized
    + FieldExpOps
    + Product
    + for<'a> Product<&'a Self>
    + Sum
    + for<'a> Sum<&'a Self>
{
    fn double(&self) -> Self {
        *self + *self
    }

    fn geom_sum(&self, p: usize) -> Self {
        let mut ans = Self::one();
        let mut prod = Self::one();

        for _ in 0..p {
            prod = prod * *self;
            ans = ans + prod;
        }

        ans
    }
}

/// # Safety
///
/// Do not use unless you are aware of the endianess in the platform you are compiling for, and the
/// Field element's representation in memory.
// TODO(Ohad): Do not compile on non-le targets.
pub unsafe trait IntoSlice<T: Sized>: Sized {
    fn into_slice(sl: &[Self]) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                sl.as_ptr() as *const T,
                std::mem::size_of_val(sl) / std::mem::size_of::<T>(),
            )
        }
    }
}

unsafe impl<F: Field> IntoSlice<u8> for F {}

pub trait ComplexConjugate {
    /// # Example
    ///
    /// ```
    /// use stwo_prover::core::fields::m31::P;
    /// use stwo_prover::core::fields::qm31::QM31;
    /// use stwo_prover::core::fields::ComplexConjugate;
    ///
    /// let x = QM31::from_u32_unchecked(1, 2, 3, 4);
    /// assert_eq!(
    ///     x.complex_conjugate(),
    ///     QM31::from_u32_unchecked(1, 2, P - 3, P - 4)
    /// );
    /// ```
    fn complex_conjugate(&self) -> Self;
}

pub trait ExtensionOf<F: Field>: Field + From<F> + NumOps<F> + NumAssignOps<F> {
    const EXTENSION_DEGREE: usize;
}

impl<F: Field> ExtensionOf<F> for F {
    const EXTENSION_DEGREE: usize = 1;
}

pub trait AllConjugate {
    fn all_conj(&self) -> Vec<Self>
    where
        Self: Sized;
}

#[macro_export]
macro_rules! impl_field {
    // $($field_name:ident : $field_type:ty)
    ($field_name: ty, $field_size: ident) => {
        use std::iter::{Product, Sum};

        use itertools::max;
        use num_traits::{Num, One, Zero};
        use $crate::core::circle::CirclePoint;
        use $crate::core::fields::{
            AllConjugate, CircPolyInterpolation, Field, FieldCircPolyOps, FieldPolyOps,
        };
        impl Num for $field_name {
            type FromStrRadixErr = Box<dyn std::error::Error>;

            fn from_str_radix(_str: &str, _radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                unimplemented!(
                    "Num::from_str_radix is not implemented for {}",
                    stringify!($field_name)
                );
            }
        }

        impl Field for $field_name {}

        impl FieldPolyOps for Vec<$field_name> {
            type Field = $field_name;

            fn mul_polys(&self, other: &Self) -> Self {
                if self.len() + other.len() == 0 {
                    return vec![];
                }

                let mut o = vec![Self::Field::zero(); self.len() + other.len() - 1];
                for i in 0..self.len() {
                    for j in 0..other.len() {
                        o[i + j] += self[i] * other[j];
                    }
                }

                o
            }

            fn add_polys(&self, other: &Self) -> Self {
                let max_iter = max([self.len(), other.len()]).unwrap();
                let mut res = vec![];

                for i in 0..max_iter {
                    let a_i = if i < self.len() {
                        self[i]
                    } else {
                        Self::Field::zero()
                    };
                    let b_i = if i < other.len() {
                        other[i]
                    } else {
                        Self::Field::zero()
                    };
                    res.push(a_i + b_i);
                }

                res
            }

            fn sub_polys(&self, other: &Self) -> Self {
                let max_iter = max([self.len(), other.len()]).unwrap();
                let mut res = vec![];

                for i in 0..max_iter {
                    let a_i = if i < self.len() {
                        self[i]
                    } else {
                        Self::Field::zero()
                    };
                    let b_i = if i < other.len() {
                        other[i]
                    } else {
                        Self::Field::zero()
                    };
                    res.push(a_i - b_i);
                }

                res
            }

            fn mul_poly_by_const(&self, constant: &Self::Field) -> Self {
                self.iter().map(|coeff| *coeff * *constant).collect()
            }

            fn eval_poly_at(&self, pt: &Self::Field) -> Self::Field {
                let mut y = Self::Field::zero();
                let mut power_of_x = Self::Field::one();

                for coeff in self.iter() {
                    y += power_of_x * *coeff;
                    power_of_x = power_of_x * *pt;
                }

                y
            }
        }

        impl FieldCircPolyOps for [Vec<$field_name>; 2] {
            type Field = $field_name;

            fn mul_circ_polys(&self, other: &Self) -> Self {
                let a1b1 = self[1].mul_polys(&other[1]);

                let x = self[0].mul_polys(&other[0]).add_polys(&a1b1).sub_polys(
                    &vec![Self::Field::zero(), Self::Field::zero()]
                        .into_iter()
                        .chain(a1b1.into_iter())
                        .collect(),
                );

                let y = self[0]
                    .mul_polys(&other[1])
                    .add_polys(&self[1].mul_polys(&other[0]));

                [x, y]
            }

            fn add_circ_polys(&self, other: &Self) -> Self {
                [self[0].add_polys(&other[0]), self[1].add_polys(&other[1])]
            }

            fn sub_circ_polys(&self, other: &Self) -> Self {
                [self[0].sub_polys(&other[0]), self[1].sub_polys(&other[1])]
            }

            fn mul_circ_by_const(&self, constant: &Self::Field) -> Self {
                [
                    self[0].mul_poly_by_const(&constant),
                    self[1].mul_poly_by_const(&constant),
                ]
            }
            fn eval_circ_poly_at(&self, point: &CirclePoint<Self::Field>) -> Self::Field {
                self[0].eval_poly_at(&point.x) + self[1].eval_poly_at(&point.x) * point.y
            }

            fn circ_poly_to_int_poly(&self) -> Result<[Vec<BaseField>; 2], String> {
                let mut p0 = vec![];
                let mut p1 = vec![];

                for f in &self[0] {
                    let m = f.to_basefield();
                    if m.is_err() {
                        return Err(m.unwrap_err());
                    }

                    p0.push(m.unwrap());
                }

                for f in &self[1] {
                    let m = f.to_basefield();
                    if m.is_err() {
                        return Err(m.unwrap_err());
                    }

                    p1.push(m.unwrap());
                }

                Ok([p0, p1])
            }
        }

        impl CircPolyInterpolation for Vec<CirclePoint<$field_name>> {
            type Field = $field_name;

            fn circ_zpoly(
                &self,
                nzero: Option<CirclePoint<Self::Field>>,
                split_exts: bool,
                oods_rep: Option<usize>,
            ) -> [Vec<Self::Field>; 2]
            where
                CirclePoint<Self::Field>: AllConjugate,
            {
                let mut pts = self.clone();
                if split_exts {
                    let mut pts2 = vec![];

                    for (index, p) in pts.iter().enumerate() {
                        let mut all_conjs = p.all_conj();
                        if oods_rep.is_some() && index < oods_rep.unwrap() {
                            // TODO: refactor the entire approach so that we dont need to use
                            // this hack
                            // this is for when we have a mix of QM31 and M31 values where
                            // the M31s have been 'forced' converted to QM31s
                            // QM31 will have 4 all_conjs values while M31 will only have 1

                            if all_conjs.len() != 4 {
                                all_conjs.resize(4, all_conjs[0]);
                            }
                        }

                        pts2.append(&mut all_conjs);
                    }

                    pts = pts2;
                }

                let mut ans: [Vec<Self::Field>; 2] = [vec![Self::Field::one()], vec![]];
                for i in 0..(pts.len() / 2) {
                    ans = ans.mul_circ_polys(&pts[2 * i].line(pts[2 * i + 1]));
                }
                if pts.len() % 2 == 1 {
                    if nzero.is_some() && nzero.unwrap().x == pts[pts.len() - 1].x {
                        ans = ans.mul_circ_polys(&[
                            vec![pts[pts.len() - 1].y],
                            vec![-Self::Field::one()],
                        ]);
                    } else {
                        ans = ans.mul_circ_polys(&[
                            vec![pts[pts.len() - 1].x, -Self::Field::one()],
                            vec![],
                        ]);
                    }
                }

                ans
            }

            fn circ_lagrange_interp(
                &self,
                vals: &Vec<Self::Field>,
                normalize: bool,
            ) -> Result<[Vec<M31>; 2], String>
            where
                CirclePoint<Self::Field>: AllConjugate,
            {
                if self.len() != vals.len() {
                    return Err("Cannot interpolate".to_owned());
                }

                let mut n_pts = vec![];
                let mut n_vals = vec![];

                for i in 0..self.len() {
                    let mut p_conj = self[i].all_conj();
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
                    let pts_removed: Vec<CirclePoint<Self::Field>> = pts[..i]
                        .iter()
                        .chain(pts[i + 1..].iter())
                        .cloned()
                        .collect();

                    let pol = pts_removed.circ_zpoly(Some(pts[i]), false, None);
                    let scale = vals[i] / pol.eval_circ_poly_at(&pts[i]);
                    ans = ans.add_circ_polys(&pol.mul_circ_by_const(&scale));
                }

                if normalize && pts.len() % 2 == 0 {
                    let d = pts.len() / 2;
                    let zpol = pts.circ_zpoly(None, false, None);
                    let coef_a = if ans[1].len() >= d {
                        ans[1][d - 1]
                    } else {
                        Self::Field::zero()
                    };
                    let scale = coef_a / zpol[1][d - 1];
                    ans = ans.sub_circ_polys(&zpol.mul_circ_by_const(&scale));
                }

                for i in 0..pts.len() {
                    let eval = ans.eval_circ_poly_at(&pts[i]);
                    if eval != vals[i] {
                        return Err("Cannot interoplate".to_owned());
                    }
                }

                ans.circ_poly_to_int_poly()
            }
        }

        impl AddAssign for $field_name {
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs;
            }
        }

        impl SubAssign for $field_name {
            fn sub_assign(&mut self, rhs: Self) {
                *self = *self - rhs;
            }
        }

        impl MulAssign for $field_name {
            fn mul_assign(&mut self, rhs: Self) {
                *self = *self * rhs;
            }
        }

        impl Div for $field_name {
            type Output = Self;

            #[allow(clippy::suspicious_arithmetic_impl)]
            fn div(self, rhs: Self) -> Self::Output {
                self * rhs.inverse()
            }
        }

        impl DivAssign for $field_name {
            fn div_assign(&mut self, rhs: Self) {
                *self = *self / rhs;
            }
        }

        impl Rem for $field_name {
            type Output = Self;

            fn rem(self, _rhs: Self) -> Self::Output {
                unimplemented!("Rem is not implemented for {}", stringify!($field_name));
            }
        }

        impl RemAssign for $field_name {
            fn rem_assign(&mut self, _rhs: Self) {
                unimplemented!(
                    "RemAssign is not implemented for {}",
                    stringify!($field_name)
                );
            }
        }

        impl Product for $field_name {
            fn product<I>(mut iter: I) -> Self
            where
                I: Iterator<Item = Self>,
            {
                let first = iter.next().unwrap_or_else(Self::one);
                iter.fold(first, |a, b| a * b)
            }
        }

        impl<'a> Product<&'a Self> for $field_name {
            fn product<I>(iter: I) -> Self
            where
                I: Iterator<Item = &'a Self>,
            {
                iter.map(|&v| v).product()
            }
        }

        impl Sum for $field_name {
            fn sum<I>(mut iter: I) -> Self
            where
                I: Iterator<Item = Self>,
            {
                let first = iter.next().unwrap_or_else(Self::zero);
                iter.fold(first, |a, b| a + b)
            }
        }

        impl<'a> Sum<&'a Self> for $field_name {
            fn sum<I>(iter: I) -> Self
            where
                I: Iterator<Item = &'a Self>,
            {
                iter.map(|&v| v).sum()
            }
        }
    };
}

/// Used to extend a field (with characteristic M31) by 2.
#[macro_export]
macro_rules! impl_extension_field {
    ($field_name: ident, $extended_field_name: ty) => {
        use rand::distributions::{Distribution, Standard};
        use $crate::core::fields::ExtensionOf;

        impl ExtensionOf<M31> for $field_name {
            const EXTENSION_DEGREE: usize =
                <$extended_field_name as ExtensionOf<M31>>::EXTENSION_DEGREE * 2;
        }

        impl Add for $field_name {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                Self(self.0 + rhs.0, self.1 + rhs.1)
            }
        }

        impl Neg for $field_name {
            type Output = Self;

            fn neg(self) -> Self::Output {
                Self(-self.0, -self.1)
            }
        }

        impl Sub for $field_name {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                Self(self.0 - rhs.0, self.1 - rhs.1)
            }
        }

        impl One for $field_name {
            fn one() -> Self {
                Self(
                    <$extended_field_name>::one(),
                    <$extended_field_name>::zero(),
                )
            }
        }

        impl Zero for $field_name {
            fn zero() -> Self {
                Self(
                    <$extended_field_name>::zero(),
                    <$extended_field_name>::zero(),
                )
            }

            fn is_zero(&self) -> bool {
                *self == Self::zero()
            }
        }

        impl Add<M31> for $field_name {
            type Output = Self;

            fn add(self, rhs: M31) -> Self::Output {
                Self(self.0 + rhs, self.1)
            }
        }

        impl Add<$field_name> for M31 {
            type Output = $field_name;

            fn add(self, rhs: $field_name) -> Self::Output {
                rhs + self
            }
        }

        impl Sub<M31> for $field_name {
            type Output = Self;

            fn sub(self, rhs: M31) -> Self::Output {
                Self(self.0 - rhs, self.1)
            }
        }

        impl Sub<$field_name> for M31 {
            type Output = $field_name;

            fn sub(self, rhs: $field_name) -> Self::Output {
                -rhs + self
            }
        }

        impl Mul<M31> for $field_name {
            type Output = Self;

            fn mul(self, rhs: M31) -> Self::Output {
                Self(self.0 * rhs, self.1 * rhs)
            }
        }

        impl Mul<$field_name> for M31 {
            type Output = $field_name;

            fn mul(self, rhs: $field_name) -> Self::Output {
                rhs * self
            }
        }

        impl Div<M31> for $field_name {
            type Output = Self;

            fn div(self, rhs: M31) -> Self::Output {
                Self(self.0 / rhs, self.1 / rhs)
            }
        }

        impl Div<$field_name> for M31 {
            type Output = $field_name;

            #[allow(clippy::suspicious_arithmetic_impl)]
            fn div(self, rhs: $field_name) -> Self::Output {
                rhs.inverse() * self
            }
        }

        impl ComplexConjugate for $field_name {
            fn complex_conjugate(&self) -> Self {
                Self(self.0, -self.1)
            }
        }

        impl From<M31> for $field_name {
            fn from(x: M31) -> Self {
                Self(x.into(), <$extended_field_name>::zero())
            }
        }

        impl AddAssign<M31> for $field_name {
            fn add_assign(&mut self, rhs: M31) {
                *self = *self + rhs;
            }
        }

        impl SubAssign<M31> for $field_name {
            fn sub_assign(&mut self, rhs: M31) {
                *self = *self - rhs;
            }
        }

        impl MulAssign<M31> for $field_name {
            fn mul_assign(&mut self, rhs: M31) {
                *self = *self * rhs;
            }
        }

        impl DivAssign<M31> for $field_name {
            fn div_assign(&mut self, rhs: M31) {
                *self = *self / rhs;
            }
        }

        impl Rem<M31> for $field_name {
            type Output = Self;

            fn rem(self, _rhs: M31) -> Self::Output {
                unimplemented!("Rem is not implemented for {}", stringify!($field_name));
            }
        }

        impl RemAssign<M31> for $field_name {
            fn rem_assign(&mut self, _rhs: M31) {
                unimplemented!(
                    "RemAssign is not implemented for {}",
                    stringify!($field_name)
                );
            }
        }

        impl Distribution<$field_name> for Standard {
            // Not intended for cryptographic use. Should only be used in tests and benchmarks.
            fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> $field_name {
                $field_name(rng.gen(), rng.gen())
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use crate::core::fields::m31::M31;
    use crate::core::fields::FieldExpOps;

    #[test]
    fn test_slice_batch_inverse() {
        let mut rng = SmallRng::seed_from_u64(0);
        let elements: [M31; 16] = rng.gen();
        let expected = elements.iter().map(|e| e.inverse()).collect::<Vec<_>>();
        let mut dst = [M31::zero(); 16];

        M31::batch_inverse(&elements, &mut dst);

        assert_eq!(expected, dst);
    }

    #[test]
    #[should_panic]
    fn test_slice_batch_inverse_wrong_dst_size() {
        let mut rng = SmallRng::seed_from_u64(0);
        let elements: [M31; 16] = rng.gen();
        let mut dst = [M31::zero(); 15];

        M31::batch_inverse(&elements, &mut dst);
    }
}
