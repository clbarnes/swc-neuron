use std::cmp::Reverse;
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::iter::FromIterator;
use std::str::FromStr;

mod structures;

pub use crate::structures::{
    AnyStructure, CnicStructure, GulyasStructure, NeuromorphoStructure, StructureIdentifier,
    VnedStructure,
};

mod header;
pub use crate::header::Header;

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
pub struct SwcSample<S: StructureIdentifier> {
    pub sample_id: SampleId,
    pub structure: S,
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub radius: Radius,
    pub parent_id: Option<SampleId>,
}

impl<S: StructureIdentifier> FromStr for SwcSample<S> {
    type Err = SampleParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed = s.trim();
        let mut items = trimmed.split_whitespace();

        let sample_id = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(0))?
            .parse()?;

        let struct_int = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(1))?
            .parse::<isize>()?;
        let structure =
            S::try_from(struct_int).map_err(|_e| SampleParseError::UnknownStructure(struct_int))?;
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
        let parent_id = match items.next() {
            Some("-1") => None,
            Some(p_str) => Some(p_str.parse()?),
            None => None,
        };

        let count: usize = items.fold(0, |x, _| x + 1);
        if count > 0 {
            return Err(SampleParseError::IncorrectNumFields(7 + count));
        }

        Ok(Self {
            sample_id,
            structure,
            x,
            y,
            z,
            radius,
            parent_id,
        })
    }
}

impl<S: StructureIdentifier> ToString for SwcSample<S> {
    fn to_string(&self) -> String {
        let structure: isize = self.structure.into();
        format!(
            "{} {} {} {} {} {} {}",
            self.sample_id,
            structure,
            self.x,
            self.y,
            self.z,
            self.radius,
            self.parent_id.map_or("-1".to_string(), |p| p.to_string()),
        )
    }
}

impl<S: StructureIdentifier> SwcSample<S> {
    fn with_ids(self, sample: SampleId, parent: Option<SampleId>) -> Self {
        SwcSample {
            sample_id: sample,
            structure: self.structure,
            x: self.x,
            y: self.y,
            z: self.z,
            radius: self.radius,
            parent_id: parent,
        }
    }
}

#[derive(Debug, Clone)]
pub struct SwcNeuron<S: StructureIdentifier, H: Header> {
    pub samples: Vec<SwcSample<S>>,
    pub header: Option<H>,
}

impl<S: StructureIdentifier, H: Header> FromIterator<SwcSample<S>> for SwcNeuron<S, H> {
    fn from_iter<I: IntoIterator<Item = SwcSample<S>>>(iter: I) -> Self {
        SwcNeuron {
            samples: iter.into_iter().collect(),
            header: None,
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum SwcParseError {
    #[error("Line read error")]
    ReadError(#[from] std::io::Error),
    #[error("Sample parse error")]
    SampleParseError(#[from] SampleParseError),
    #[error("Header parse error")]
    HeaderParseError(String),
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

impl<S: StructureIdentifier, H: Header> SwcNeuron<S, H> {
    /// Sort the neuron's samples by their index.
    pub fn sort_index(mut self) -> Self {
        self.samples
            .sort_unstable_by(|a, b| a.sample_id.cmp(&b.sample_id));
        self
    }

    /// Re-index the neuron's samples in order of occurrence, starting at 1.
    /// Returns error if the SWC is missing a parent sample
    pub fn reindex(self) -> Result<Self, MissingSampleError> {
        let old_to_new: HashMap<SampleId, SampleId> = self
            .samples
            .iter()
            .enumerate()
            .map(|(idx, row)| (row.sample_id, idx + 1))
            .collect();

        let mut samples = Vec::with_capacity(self.samples.len());
        for (idx, row) in self.samples.into_iter().enumerate() {
            let parent;
            if let Some(old) = row.parent_id {
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

        Ok(Self {
            samples,
            header: self.header,
        })
    }

    /// Re-order its samples in pre-order depth first search.
    /// Children are visited in the order of their original sample number.
    ///
    /// Returns an error if the neuron is not a self-consistent tree.
    pub fn sort_topo(self, reindex: bool) -> Result<Self, InconsistentNeuronError> {
        // as indices into the original samples vec
        let mut parent_to_children: HashMap<SampleId, Vec<SampleId>> =
            HashMap::with_capacity(self.samples.len());
        let mut id_to_sample: HashMap<SampleId, SwcSample<S>> =
            HashMap::with_capacity(self.samples.len());
        let mut root = None;

        for row in self.samples {
            if let Some(p) = row.parent_id {
                let entry = parent_to_children.entry(p).or_insert_with(Vec::default);
                entry.push(row.sample_id);
                id_to_sample
                    .insert(row.sample_id, row)
                    .ok_or_else(|| InconsistentNeuronError::DuplicateSampleError(row.sample_id))?;
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
            let children = parent_to_children.remove(&r.sample_id).map_or_else(
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
                to_visit.extend(children.into_iter().map(|c| (r.sample_id, c)));
            }
        } else {
            return Err(InconsistentNeuronError::NoRootError);
        }

        while let Some((parent_id, row_id)) = to_visit.pop() {
            let row = id_to_sample
                .remove(&row_id)
                .expect("Just constructed this vec");
            let children = parent_to_children.remove(&row.sample_id).map_or_else(
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
                to_visit.extend(children.into_iter().map(|c| (row.sample_id, c)));
            }
        }

        if id_to_sample.is_empty() {
            Ok(SwcNeuron {
                samples,
                header: self.header,
            })
        } else {
            Err(InconsistentNeuronError::DisconnectedError)
        }
    }

    pub fn from_reader<R: Read>(reader: R) -> Result<Self, SwcParseError> {
        let buf = BufReader::new(reader);

        let mut samples = Vec::default();
        let mut is_header = true;
        let mut header_lines = Vec::default();
        for result in buf.lines() {
            let raw_line = result.map_err(SwcParseError::ReadError)?;
            let line = raw_line.trim();
            if line.starts_with('#') {
                if is_header {
                    header_lines.push(line.trim_start_matches('#').trim_start().to_string());
                }
                continue;
            }
            is_header = false;
            if line.is_empty() {
                continue;
            }
            samples.push(SwcSample::from_str(&line)?);
        }

        let header: Option<H>;

        if header_lines.is_empty() {
            header = None;
        } else {
            let header_str = header_lines.join("\n");
            header = Some(header_str
                .parse()
                .map_err(|_e| SwcParseError::HeaderParseError(header_str))?);
        }

        Ok(Self {
            samples,
            header,
        })
    }

    pub fn to_writer<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        let mut w = BufWriter::new(writer);
        if let Some(h) = self.header.clone() {
            for line in h.to_string().lines() {
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

    /// Replace the existing header with a new one, returning the existing.
    pub fn replace_header(&mut self, header: Option<H>) -> Option<H> {
        std::mem::replace(&mut self.header, header)
    }
}
