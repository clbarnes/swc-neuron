use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
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

/// Error in parsing a SWC sample (row).
#[derive(thiserror::Error, Debug)]
pub enum SampleParseError {
    /// A field which should be an integer could not be parsed.
    #[error("Integer field parse error")]
    IntField(#[from] std::num::ParseIntError),
    /// A field which should be a float/ decimal could not be parsed.
    #[error("Float field parse error")]
    FloatField(#[from] std::num::ParseFloatError),
    /// The value of the `structure` field was not recognised.
    /// Not checked for structure enums with a catch-all variant.
    #[error("Reference to unknown structure {0}")]
    UnknownStructure(isize),
    /// Line terminated early; more fields expected.
    #[error("Incorrect number of fields: found {0}")]
    IncorrectNumFields(usize),
}

/// Struct representing a row of a SWC file (a single sample from the neuron),
/// which gives information about a single node in the tree.
///
/// If the `parent_id` is None, this is a root node.
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
    /// Create a new [SwcSample] with  different sample and parent IDs.
    ///
    /// The other features are the same.
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

/// Struct representing a neuron skeleton as a tree of [SwcSample]s.
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

/// Error for a SWC file which cannot be parsed
#[derive(thiserror::Error, Debug)]
pub enum SwcParseError {
    /// A line could not be read from the file.
    #[error("Line read error")]
    Read(#[from] std::io::Error),
    /// The line could not be parsed as a SwcSample.
    #[error("Sample parse error")]
    SampleParse(#[from] SampleParseError),
    /// The SWC header could not be parsed.
    #[error("Header parse error")]
    HeaderParse(String),
}

/// Error where a sample refers to an unknown parent sample.
#[derive(thiserror::Error, Debug)]
#[error("Parent sample {parent_sample} does not exist")]
pub struct MissingSampleError {
    parent_sample: usize,
}

/// Error where a neuron represented by a SWC file is inconsistent.
#[derive(thiserror::Error, Debug)]
pub enum InconsistentNeuronError {
    /// Neuron is not a tree as it has multiple roots (parentless nodes).
    #[error("Neuron has >1 root")]
    MultipleRoots,
    /// Neuron is not a tree as it has several disconnected parts.
    #[error("Neuron has >1 connected component")]
    Disconnected,
    /// Neuron has no root: it could be empty or be cyclic.
    #[error("Neuron has no root")]
    NoRootError,
    /// Samples refer to unknown parent samples.
    #[error("Neuron has missing sample(s)")]
    MissingSample(#[from] MissingSampleError),
    /// Samples have clashing IDs.
    #[error("Neuron has multiple samples numbered {0}")]
    DuplicateSample(SampleId),
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
                        .ok_or(MissingSampleError { parent_sample: old })?,
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
                let entry = parent_to_children.entry(p).or_default();
                entry.push(row.sample_id);
                id_to_sample
                    .insert(row.sample_id, row)
                    .ok_or(InconsistentNeuronError::DuplicateSample(row.sample_id))?;
            } else if root.is_some() {
                return Err(InconsistentNeuronError::MultipleRoots);
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
            Err(InconsistentNeuronError::Disconnected)
        }
        // todo: possible MissingSampleError
    }

    /// Ensure that [SwcNeuron] is a self-consistent tree.
    ///
    /// If `ignore_order` is `true`, samples' parents must be defined before they are.
    pub fn validate(&self, ignore_order: bool) -> Result<(), InconsistentNeuronError> {
        use InconsistentNeuronError::*;

        // use sample IDs
        let mut parent_to_children: HashMap<SampleId, Vec<SampleId>> =
            HashMap::with_capacity(self.samples.len());
        let mut sample_ids: HashSet<usize> = HashSet::with_capacity(self.samples.len());
        let mut root = None;

        for row in self.samples.iter() {
            if !sample_ids.insert(row.sample_id) {
                return Err(DuplicateSample(row.sample_id));
            }
            if let Some(p) = row.parent_id {
                if !ignore_order && !sample_ids.contains(&p) {
                    return Err(MissingSample(MissingSampleError { parent_sample: p }));
                }
                let entry = parent_to_children.entry(p).or_default();
                entry.push(row.sample_id);
            } else if root.is_some() {
                return Err(MultipleRoots);
            } else {
                root = Some(row.sample_id);
            }
        }

        let Some(rt) = root else {
            return Err(NoRootError);
        };

        let mut to_visit = Vec::default();
        to_visit.push(rt);

        while let Some(sample_id) = to_visit.pop() {
            let children = parent_to_children
                .remove(&sample_id)
                .unwrap_or_else(|| Vec::with_capacity(0));
            to_visit.extend(children.into_iter());
        }

        if parent_to_children.is_empty() {
            Ok(())
        } else if let Some((unknown_p, _)) = parent_to_children
            .iter()
            .take_while(|(p, _)| !sample_ids.contains(p))
            .next()
        {
            Err(MissingSample(MissingSampleError {
                parent_sample: *unknown_p,
            }))
        } else {
            Err(Disconnected)
        }
    }

    /// Parse a [SwcNeuron] from a [Read]er.
    ///
    /// Does not check the neuron for consistency, but does check for valid structures.
    pub fn from_reader<R: Read>(reader: R) -> Result<Self, SwcParseError> {
        let buf = BufReader::new(reader);

        let mut samples = Vec::default();
        let mut is_header = true;
        let mut header_lines = Vec::default();
        for result in buf.lines() {
            let raw_line = result.map_err(SwcParseError::Read)?;
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
            samples.push(SwcSample::from_str(line)?);
        }

        let header: Option<H> = if header_lines.is_empty() {
            None
        } else {
            let header_str = header_lines.join("\n");
            Some(
                header_str
                    .parse()
                    .map_err(|_e| SwcParseError::HeaderParse(header_str))?,
            )
        };

        Ok(Self { samples, header })
    }

    /// Dump this [SwcNeuron] to a [Write]r.
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
