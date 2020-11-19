use std::collections::HashMap;
use std::fmt::Debug;
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::iter::FromIterator;
use std::str::FromStr;
use std::cmp::Reverse;

mod structures;

pub use crate::structures::{
    AnyStructure, CnicStructure, GulyasStructure, NeuromorphoStructure, StructureIdentifier,
    VnedStructure,
};
// #[cfg(feature = "cli")]
// pub mod bin;

type SampleId = usize;
type Radius = f64;

#[derive(thiserror::Error, Debug)]
pub enum SampleParseError {
    #[error("Integer field parse error")]
    IntFieldError(#[from] std::num::ParseIntError),
    #[error("Float field parse error")]
    FloatFieldError(#[from] std::num::ParseFloatError),
    #[error("Reference to unknown structure {0}")]
    UnknownStructure(isize),
    #[error("Incorrect number of fields: found {0}")]
    IncorrectNumFields(usize),
}

#[derive(Debug, Clone, Copy)]
pub struct SwcSample<T: StructureIdentifier> {
    pub sample: SampleId,
    pub structure: T,
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub radius: Radius,
    pub parent: Option<SampleId>,
}

impl<T: StructureIdentifier> FromStr for SwcSample<T> {
    type Err = SampleParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed = s.trim();
        let mut items = trimmed.split_whitespace();

        let sample = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(0))?
            .parse()?;

        let struct_int = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(1))?
            .parse::<isize>()?;
        let structure =
            T::try_from(struct_int).map_err(|_e| SampleParseError::UnknownStructure(struct_int))?;
        let x = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(2))?
            .parse::<f64>()?;
        let y = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(3))?
            .parse::<f64>()?;
        let z = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(4))?
            .parse::<f64>()?;
        let radius = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(5))?
            .parse::<f64>()?;
        let parent = match items.next() {
            Some(p_str) => Some(p_str.parse()?),
            None => None,
        };

        Ok(Self {
            sample,
            structure,
            x,
            y,
            z,
            radius,
            parent,
        })
    }
}

impl<T: StructureIdentifier> ToString for SwcSample<T> {
    fn to_string(&self) -> String {
        let structure: isize = self.structure.into();
        let mut s = format!(
            "{} {} {} {} {} {}",
            self.sample, structure, self.x, self.y, self.z, self.radius
        );
        if let Some(p) = self.parent {
            s = format!("{} {}", s, p)
        }
        s
    }
}

impl<T: StructureIdentifier> SwcSample<T> {
    fn with_ids(self, sample: SampleId, parent: Option<SampleId>) -> Self {
        SwcSample {
            sample,
            structure: self.structure,
            x: self.x,
            y: self.y,
            z: self.z,
            radius: self.radius,
            parent,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SwcNeuron<T: StructureIdentifier> {
    pub samples: Vec<SwcSample<T>>,
}

impl<T: StructureIdentifier> FromIterator<SwcSample<T>> for SwcNeuron<T> {
    fn from_iter<I: IntoIterator<Item = SwcSample<T>>>(iter: I) -> Self {
        SwcNeuron {
            samples: iter.into_iter().collect(),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum SwcParseError {
    #[error("Line read error")]
    ReadError(#[from] std::io::Error),
    #[error("Sample parse error")]
    SampleParseError(#[from] SampleParseError),
}

#[derive(thiserror::Error, Debug)]
#[error("Parent sample {parent_sample} does not exist")]
pub struct MissingSampleError {
    parent_sample: usize,
}

#[derive(thiserror::Error, Debug)]
pub enum InconsistentNeuronError {
    #[error("Neuron has >1 root")]
    MultipleRootsError,
    #[error("Neuron has >1 connected component")]
    DisconnectedError,
    #[error("Neuron has no root")]
    NoRootError,
    #[error("Neuron has missing sample(s)")]
    MissingSampleError(#[from] MissingSampleError),
    #[error("Neuron has multiple samples numbered {0}")]
    DuplicateSampleError(SampleId),
}

impl<T: StructureIdentifier> SwcNeuron<T> {
    /// Sort the neuron's samples by their index.
    pub fn sort_index(mut self) -> Self {
        self.samples
            .sort_unstable_by(|a, b| a.sample.cmp(&b.sample));
        self
    }

    /// Re-index the neuron's samples in order of occurrence, starting at 1.
    /// Returns error if the SWC is missing a parent sample
    pub fn reindex(self) -> Result<Self, MissingSampleError> {
        let old_to_new: HashMap<SampleId, SampleId> = self
            .samples
            .iter()
            .enumerate()
            .map(|(idx, row)| (row.sample, idx + 1))
            .collect();

        let mut samples = Vec::with_capacity(self.samples.len());
        for (idx, row) in self.samples.into_iter().enumerate() {
            let parent;
            if let Some(old) = row.parent {
                parent = Some(
                    *old_to_new
                        .get(&old)
                        .ok_or_else(|| MissingSampleError { parent_sample: old })?,
                );
            } else {
                parent = None;
            }
            samples.push(row.with_ids(idx + 1, parent));
        }

        Ok(Self { samples })
    }

    /// Re-order its samples in pre-order depth first search.
    /// Children are visited in the order of their original sample number.
    ///
    /// Returns an error if the neuron is not a self-consistent tree.
    pub fn sort_topo(self, reindex: bool) -> Result<Self, InconsistentNeuronError> {
        // as indices into the original samples vec
        let mut parent_to_children: HashMap<SampleId, Vec<SampleId>> =
            HashMap::with_capacity(self.samples.len());
        let mut id_to_sample: HashMap<SampleId, SwcSample<T>> =
            HashMap::with_capacity(self.samples.len());
        let mut root = None;

        for row in self.samples {
            if let Some(p) = row.parent {
                let entry = parent_to_children.entry(p).or_insert_with(Vec::default);
                entry.push(row.sample);
                id_to_sample
                    .insert(row.sample, row)
                    .ok_or_else(|| InconsistentNeuronError::DuplicateSampleError(row.sample))?;
            } else if root.is_some() {
                    return Err(InconsistentNeuronError::MultipleRootsError);
            } else {
                root = Some(row);
            }
        }

        let mut samples = Vec::with_capacity(id_to_sample.len() + 1);

        let mut to_visit = vec![];
        let mut next_id: SampleId = 1;

        if let Some(r) = root {
            let children = parent_to_children.remove(&r.sample).map_or_else(
                || Vec::with_capacity(0),
                |mut v| {
                    v.sort_unstable_by_key(|&x| Reverse(x));
                    v
                },
            );
            if reindex {
                samples.push(r.with_ids(next_id, None));
                to_visit.extend(children.into_iter().map(|c| (next_id, c)));
                next_id += 1;
            } else {
                samples.push(r);
                to_visit.extend(children.into_iter().map(|c| (r.sample, c)));
            }
        } else {
            return Err(InconsistentNeuronError::NoRootError);
        }

        while let Some((parent_id, row_id)) = to_visit.pop() {
            let row = id_to_sample
                .remove(&row_id)
                .expect("Just constructed this vec");
            let children = parent_to_children.remove(&row.sample).map_or_else(
                || Vec::with_capacity(0),
                |mut v| {
                    v.sort_unstable_by_key(|&id| Reverse(id));
                    v
                },
            );
            if reindex {
                samples.push(row.with_ids(next_id, Some(parent_id)));
                to_visit.extend(children.into_iter().map(|c| (next_id, c)));
                next_id += 1;
            } else {
                samples.push(row);
                to_visit.extend(children.into_iter().map(|c| (row.sample, c)));
            }
        }

        if id_to_sample.is_empty() {
            Ok(SwcNeuron { samples })
        } else {
            Err(InconsistentNeuronError::DisconnectedError)
        }
    }

    pub fn from_reader<R: Read>(reader: R) -> Result<Self, SwcParseError> {
        let buf = BufReader::new(reader);

        let mut samples = Vec::default();
        for result in buf.lines() {
            let raw_line = result.map_err(SwcParseError::ReadError)?;
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let sample: SwcSample<T> = match SwcSample::from_str(&line) {
                Err(SampleParseError::IncorrectNumFields(0)) => continue,
                other => other,
            }?;
            samples.push(sample);
        }

        Ok(Self { samples })
    }

    pub fn to_writer<W: Write>(
        &self,
        writer: &mut W,
        header: Option<&str>,
    ) -> Result<(), std::io::Error> {
        let mut w = BufWriter::new(writer);
        if let Some(s) = header {
            for line in s.lines() {
                if !line.starts_with('#') {
                    writeln!(w, "# {}", line)?;
                } else {
                    writeln!(w, "{}", line)?;
                }
            }
        }
        for s in self.samples.iter() {
            writeln!(w, "{}", s.to_string())?;
        }
        Ok(())
    }
}
