#![allow(dead_code)]

use std::collections::HashMap;
use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use super::fields::m31::BaseField;
use super::vcs::ops::{MerkleHasher, MerkleOps};

#[derive(Debug)]
pub struct SimpleMerkleTree<B: MerkleOps<H>, H: MerkleHasher> {
    nodes: Vec<Vec<H::Hash>>,
    leaves: Vec<H::Hash>,
    phantom: PhantomData<B>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
pub struct BatchMerkleProof<H: MerkleHasher> {
    proof: Vec<Vec<H::Hash>>,
    positions: Vec<Vec<bool>>,
    indices: Vec<usize>,
    leaves: Vec<H::Hash>,
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

    pub fn generate_batch_proof(&self, indices: &[usize]) -> BatchMerkleProof<H> {
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

                if sibling_idx < self.nodes[level].len() && !used_indices[sibling_idx] {
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

        BatchMerkleProof::<H> {
            proof,
            positions,
            indices: indices.to_vec(),
            leaves: indices.iter().map(|&i| self.leaves[i]).collect(),
        }
    }
}

impl<H: MerkleHasher> BatchMerkleProof<H> {
    pub fn verify(&self, root: H::Hash, opened_values: &Vec<BaseField>) -> bool {
        let matched_opened_values = opened_values
            .iter()
            .zip(self.leaves.iter())
            .all(|(o, l)| H::hash(*o) == *l);

        if !matched_opened_values {
            return false;
        }

        // Create mapping to handle duplicates while preserving order
        let mut seen = HashMap::new();
        let mut unique_pairs: Vec<(usize, H::Hash)> = Vec::new();

        for (i, (&idx, &leaf)) in self.indices.iter().zip(self.leaves.iter()).enumerate() {
            if !seen.contains_key(&idx) {
                seen.insert(idx, i);
                unique_pairs.push((idx, leaf));
            }
        }

        let mut current_level = unique_pairs;
        let mut proof_idx = 0;

        for (level_proof, level_positions) in self.proof.iter().zip(self.positions.iter()) {
            let mut next_level = Vec::new();
            let mut processed_indices = vec![false; current_level.len()];

            for (i, &(idx, hash)) in current_level.iter().enumerate() {
                if processed_indices[i] {
                    continue;
                }
                processed_indices[i] = true;

                let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
                let parent_idx = idx / 2;

                let mut pair_found = false;
                for (j, &(other_idx, other_hash)) in current_level.iter().enumerate() {
                    if !processed_indices[j] && other_idx == sibling_idx {
                        if idx % 2 == 0 {
                            next_level
                                .push((parent_idx, H::hash_node(Some((hash, other_hash)), &[])));
                        } else {
                            next_level
                                .push((parent_idx, H::hash_node(Some((other_hash, hash)), &[])));
                        }
                        processed_indices[j] = true;
                        pair_found = true;
                        break;
                    }
                }

                if !pair_found && proof_idx < level_proof.len() {
                    if level_positions[seen[&idx]] {
                        next_level.push((
                            parent_idx,
                            H::hash_node(Some((hash, level_proof[proof_idx])), &[]),
                        ));
                    } else {
                        next_level.push((
                            parent_idx,
                            H::hash_node(Some((level_proof[proof_idx], hash)), &[]),
                        ));
                    }
                    proof_idx += 1;
                }
            }

            current_level = next_level;
        }

        current_level.len() == 1 && current_level[0].1 == root
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::backend::CpuBackend;
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
        let proof = tree.generate_batch_proof(&indices);

        let opened_values = indices.iter().map(|&i| values[i]).collect::<Vec<_>>();
        assert!(proof.verify(root, &opened_values));
    }
}
