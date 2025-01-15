#![allow(dead_code)]

use std::collections::HashMap;
use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use super::fields::m31::BaseField;
use super::vcs::ops::{MerkleHasher, MerkleOps};

#[derive(Debug, Clone)]
pub struct SimpleMerkleTree<B: MerkleOps<H>, H: MerkleHasher> {
    nodes: Vec<Vec<H::Hash>>,
    leaves: Vec<H::Hash>,
    phantom: PhantomData<B>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
pub struct MerkleProof<H: MerkleHasher> {
    pub proof: Vec<Vec<H::Hash>>,
    pub positions: Vec<Vec<bool>>,
    pub indices: Vec<usize>,
    pub leaves: Vec<H::Hash>,
}

impl<B: MerkleOps<H>, H: MerkleHasher> SimpleMerkleTree<B, H> {
    pub fn new(values: &Vec<BaseField>) -> Self {
        let leaves = values
            .iter()
            .map(|value| Self::hash(*value))
            .collect::<Vec<_>>();

        let mut tree = Self {
            nodes: vec![leaves.clone()],
            leaves,
            phantom: PhantomData,
        };
        tree.build();
        tree
    }

    fn hash(data: BaseField) -> H::Hash {
        H::hash(data)
    }

    fn build(&mut self) {
        while self.nodes.last().unwrap().len() > 1 {
            let current_level = self.nodes.last().unwrap();
            let mut next_level = Vec::new();

            for chunk in current_level.chunks(2) {
                if chunk.len() == 2 {
                    next_level.push(H::hash_node(Some((chunk[0], chunk[1])), &[]));
                } else {
                    next_level.push(chunk[0]);
                }
            }

            self.nodes.push(next_level);
        }
    }

    pub fn root(&self) -> H::Hash {
        self.nodes.last().unwrap()[0]
    }

    pub fn generate_proofs(&self, indices: &Vec<usize>) -> Vec<MerkleProof<H>> {
        indices.iter().map(|&i| self.generate_proof(i)).collect()
    }

    pub fn generate_proof(&self, index: usize) -> MerkleProof<H> {
        let mut proof = Vec::new();
        let mut positions = Vec::new();
        let mut current_index = index;

        for level in 0..self.nodes.len() - 1 {
            let mut level_proof = Vec::new();
            let mut level_positions = Vec::new();

            let sibling_idx = if current_index % 2 == 0 {
                current_index + 1
            } else {
                current_index - 1
            };

            if sibling_idx < self.nodes[level].len() {
                level_proof.push(self.nodes[level][sibling_idx]);
                level_positions.push(current_index % 2 == 0);
            }

            proof.push(level_proof);
            positions.push(level_positions);
            current_index /= 2;
        }

        MerkleProof {
            proof,
            positions,
            indices: vec![index],
            leaves: vec![self.nodes[0][index]],
        }
    }

    pub fn generate_batch_proof(&self, indices: &[usize]) -> MerkleProof<H> {
        let mut proof = Vec::new();
        let mut positions = Vec::new();

        // Track unique indices while preserving order of first occurrence
        let mut seen = HashMap::new();
        let mut unique_indices: Vec<usize> = Vec::new();
        for (i, &idx) in indices.iter().enumerate() {
            if !seen.contains_key(&idx) {
                seen.insert(idx, i);
                unique_indices.push(idx);
            }
        }

        let mut current_indices = unique_indices;
        let mut used_indices = vec![false; self.leaves.len()];

        for &idx in &current_indices {
            used_indices[idx] = true;
        }

        for level in 0..self.nodes.len() - 1 {
            let mut level_proof = Vec::new();
            let mut level_positions = vec![false; indices.len()];
            let mut next_indices = Vec::new();
            let mut processed = vec![false; self.nodes[level].len()];

            for &idx in &current_indices {
                if processed[idx] {
                    continue;
                }
                processed[idx] = true;

                let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };

                if sibling_idx < self.nodes[level].len() && !processed[sibling_idx] {
                    level_proof.push(self.nodes[level][sibling_idx]);
                    // Set position for all occurrences of this index
                    for (orig_idx, &orig_pos) in indices.iter().enumerate() {
                        if orig_pos == idx {
                            level_positions[orig_idx] = idx % 2 == 0;
                        }
                    }
                }

                next_indices.push(idx / 2);
            }

            proof.push(level_proof);
            positions.push(level_positions);
            current_indices = next_indices;
        }

        MerkleProof::<H> {
            proof,
            positions,
            indices: indices.to_vec(),
            leaves: indices.iter().map(|&i| self.leaves[i]).collect(),
        }
    }
}

impl<H: MerkleHasher> MerkleProof<H> {
    pub fn verify(&self, root: H::Hash, value: BaseField) -> bool {
        let mut current_leaf = self.leaves[0];

        if H::hash(value) != current_leaf {
            return false;
        }

        let mut current_indices = self.indices[0];
        for layer in self.proof.iter() {
            let sibling_idx = if current_indices % 2 == 0 {
                current_indices + 1
            } else {
                current_indices - 1
            };
            let sibling_hash = layer[0];
            if sibling_idx < current_indices {
                current_leaf = H::hash_node(Some((sibling_hash, current_leaf)), &[]);
            } else {
                current_leaf = H::hash_node(Some((current_leaf, sibling_hash)), &[]);
            }

            current_indices = current_indices / 2;
        }

        current_leaf == root
    }
}

pub fn verify_many_proof<H: MerkleHasher>(
    proofs: &Vec<MerkleProof<H>>,
    root: H::Hash,
    opened_values: &Vec<BaseField>,
) -> bool {
    proofs
        .iter()
        .zip(opened_values.iter())
        .all(|(proof, value)| proof.verify(root, *value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::backend::CpuBackend;
    use crate::core::fields::m31::M31;
    use crate::core::vcs::blake2_merkle::Blake2sMerkleHasher;

    #[test]
    fn test_batch_merkle_proof() {
        // Create sample leaves
        let values = vec![
            BaseField::from(1),
            BaseField::from(2),
            BaseField::from(3),
            BaseField::from(4),
            BaseField::from(5),
            BaseField::from(6),
            BaseField::from(7),
            BaseField::from(8),
        ];

        let tree = SimpleMerkleTree::<CpuBackend, Blake2sMerkleHasher>::new(&values);
        let root = tree.root();

        // Test with unsorted and duplicated indices
        let indices = vec![5, 2, 7, 1, 3, 2, 5, 7];
        let proofs = tree.generate_proofs(&indices);

        let opened_values = indices.iter().map(|&i| values[i]).collect::<Vec<_>>();
        println!("opened_values: {:?}", opened_values);

        assert!(verify_many_proof(&proofs, root, &opened_values));
        // assert!(proof.verify(root, &opened_values));
    }

    #[test]
    fn test_batch_merkle_proof_verify2() {
        let values = vec![
            M31(602288748),
            M31(1755808594),
            M31(678509178),
            M31(1399301630),
            M31(1300682691),
            M31(73959714),
            M31(143257633),
            M31(1945249805),
            M31(786927801),
            M31(43035029),
            M31(203029012),
            M31(1598422269),
            M31(1118783692),
            M31(433007269),
            M31(1437610480),
            M31(1839425160),
            M31(713980251),
            M31(10415707),
            M31(1169925666),
            M31(1542860774),
            M31(1375837404),
            M31(2013307452),
            M31(677230559),
            M31(1445667943),
            M31(1853854807),
            M31(2066183936),
            M31(983670015),
            M31(602177832),
            M31(734094945),
            M31(640832268),
            M31(249747530),
            M31(1863195319),
            M31(1510516216),
            M31(1235082060),
            M31(1440751414),
            M31(1972200690),
            M31(1963915168),
            M31(899023322),
            M31(1053735816),
            M31(8091360),
            M31(865062991),
            M31(906205346),
            M31(1210555157),
            M31(61358409),
            M31(576980408),
            M31(1749019103),
            M31(393951486),
            M31(1167091139),
            M31(904829637),
            M31(480445739),
            M31(455061367),
            M31(1175731264),
            M31(2120505166),
            M31(11648756),
            M31(709797470),
            M31(848150830),
            M31(1242040684),
            M31(1380986592),
            M31(1608022750),
            M31(963778916),
            M31(1360979264),
            M31(855332825),
            M31(766119299),
            M31(1372741300),
            M31(1942732852),
            M31(1515244120),
            M31(1168260208),
            M31(1300075566),
            M31(2096220229),
            M31(121248866),
            M31(2085247091),
            M31(690182953),
            M31(547252943),
            M31(1955059126),
            M31(315540234),
            M31(1805249102),
            M31(1778899692),
            M31(978715846),
            M31(140382779),
            M31(1239278667),
            M31(1448176505),
            M31(270083039),
            M31(2004166375),
            M31(1159390504),
            M31(365140357),
            M31(1535344259),
            M31(140967377),
            M31(192720870),
            M31(413773641),
            M31(550293776),
            M31(371471913),
            M31(455098104),
            M31(1590343866),
            M31(1765274930),
            M31(2086642536),
            M31(279943281),
            M31(1857426214),
            M31(1161798161),
            M31(1622986812),
            M31(260477112),
            M31(1221273105),
            M31(810516766),
            M31(894986709),
            M31(1241457785),
            M31(1940326091),
            M31(519534982),
            M31(223204907),
            M31(27280341),
            M31(787473519),
            M31(1641780443),
            M31(711192913),
            M31(1118299364),
            M31(2110330404),
            M31(328899668),
            M31(1103018587),
            M31(194492588),
            M31(1030093916),
            M31(162827729),
            M31(1748852274),
            M31(711032807),
            M31(592650190),
            M31(1120076627),
            M31(645367083),
            M31(764480038),
            M31(2048795896),
            M31(1073779008),
            M31(1621508428),
            M31(967350983),
        ];
        let tree = SimpleMerkleTree::<CpuBackend, Blake2sMerkleHasher>::new(&values);
        let root = tree.root();

        let indices = vec![
            64, 8, 76, 78, 80, 24, 92, 94, 96, 40, 108, 110, 112, 56, 124, 126,
        ];
        // let indices = vec![1];
        let proofs = tree.generate_proofs(&indices);

        let opened_values = indices.iter().map(|&i| values[i]).collect::<Vec<_>>();
        println!("opened_values: {:?}", opened_values);

        assert!(verify_many_proof(&proofs, root, &opened_values));
    }
}
