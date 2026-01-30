//! Rust library for reading, writing, and manipulating SWC files for neuronal morphology.
//! Also includes a CLI for basic validation, sorting, and reindexing (with optional feature `cli`).
//!
//! The format was originally proposed in [Cannon, et al. 1998](http://dx.doi.org/10.1016/S0165-0270(98)00091-0),
//! with an implementation in [dohalloran/SWC_BATCH_CHECK](https://github.com/dohalloran/SWC_BATCH_CHECK).
//!
//! While commonly used, many variants exist; this implementation tries to cover the "standardised" version described
//! [here](http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html),
//! with some ambiguities resolved by the [SWCplus specification](https://neuroinformatics.nl/swcPlus/).
//!
//! The header is a series of `#`-prefixed lines starting at the beginning of the file.
//! Blank lines (i.e. without a `#` or any other non-whitespace content) do not interrupt the header,
//! but are also not included in the parsed header.
//! All other `#`-prefixed and all whitespace-only lines in the file after the first sample are ignored.
//! Samples define a sample ID, a structure represented by that sample, its location, radius,
//! and the sample ID of the sample's parent in the neuron's tree structure (the root's parent is `-1`).
//!
//! The [SwcNeuron] is generic over implementors of [StructureIdentifier] and [Header],
//! and can be parsed from [Read]ers and dumped to [Write]rs.
//! [StructureIdentifier] is implemented for some known sub-specifications.
//! [Header] is implemented for [String] (i.e. a free-text header field).
//! [AnySwc] is a [SwcNeuron] with any structure integer and string header.

#![warn(missing_docs)]
use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};
use std::convert::{TryFrom, TryInto};
use std::error::Error;
use std::fmt::{Debug, Display};
use std::io::{self, BufRead, Lines, Write};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::str::FromStr;

pub mod structures;

pub use crate::structures::{AnyStructure, StructureIdentifier};

pub mod header;
pub use crate::header::Header;

/// Type used for sample IDs.
///
/// SWC files use -1 for the parent ID of the root sample,
/// but this package uses a signed ID type with the root's parent as `None`.
pub type SampleId = u64;

/// Float type used for locations and radii.
pub type Precision = f64;
type Radius = Precision;

/// Maximally flexible [SwcNeuron] with any structure specification and a free-text header.
pub type AnySwc = SwcNeuron<AnyStructure, String>;

pub(crate) const HEADER_BUF_LEN: usize = 512;

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
    /// ID of the SWC sample
    pub sample_id: SampleId,
    /// SWC structure enum
    pub structure: S,
    /// X location
    pub x: Precision,
    /// Y location
    pub y: Precision,
    /// Z location
    pub z: Precision,
    /// Radius of the neuron at this sample
    pub radius: Radius,
    /// ID of the parent sample (None if this is the root)
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
            .parse::<Precision>()?;
        let y = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(3))?
            .parse::<Precision>()?;
        let z = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(4))?
            .parse::<Precision>()?;
        let radius = items
            .next()
            .ok_or(SampleParseError::IncorrectNumFields(5))?
            .parse::<Radius>()?;
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

impl<S: StructureIdentifier> Display for SwcSample<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let structure: isize = self.structure.into();
        write!(
            f,
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
    /// Samples present in the SWC file.
    pub samples: Vec<SwcSample<S>>,
    /// Header of the SWC file
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
    parent_sample: SampleId,
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
    /// Number of samples in the neuron.
    pub fn len(&self) -> usize {
        self.samples.len()
    }

    /// Whether there are any samples in the neuron.
    pub fn is_empty(&self) -> bool {
        self.samples.is_empty()
    }

    /// Sort the neuron's samples by their index.
    pub fn sort_index(mut self) -> Self {
        self.samples
            .sort_unstable_by(|a, b| a.sample_id.cmp(&b.sample_id));
        self
    }

    /// Re-index the neuron's samples in order of occurrence, starting at the given ID and incrementing.
    /// Returns error if the SWC is missing a parent sample
    pub fn reindex_from(self, first_id: SampleId) -> Result<Self, MissingSampleError> {
        let old_to_new: HashMap<SampleId, SampleId> = self
            .samples
            .iter()
            .enumerate()
            .map(|(idx, row)| (row.sample_id, idx as SampleId + first_id))
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
            samples.push(row.with_ids(idx as u64 + 1, parent));
        }

        Ok(Self {
            samples,
            header: self.header,
        })
    }

    /// Re-index the neuron's samples in order of occurrence, starting at 1.
    /// Returns error if the SWC is missing a parent sample
    pub fn reindex(self) -> Result<Self, MissingSampleError> {
        self.reindex_from(1)
    }

    /// Re-order its samples in pre-order depth first search.
    /// Children are visited in the order of their original sample number.
    ///
    /// Returns an error if the neuron is not a self-consistent tree.
    pub fn sort_topo(self, reindex: bool) -> Result<Self, InconsistentNeuronError> {
        let mut parent_to_children: HashMap<SampleId, Vec<SampleId>> =
            HashMap::with_capacity(self.samples.len());
        let mut id_to_sample: HashMap<SampleId, SwcSample<S>> =
            HashMap::with_capacity(self.samples.len());
        let mut root = None;

        for row in self.samples {
            if let Some(p) = row.parent_id {
                let entry = parent_to_children.entry(p).or_default();
                entry.push(row.sample_id);
                if id_to_sample.insert(row.sample_id, row).is_some() {
                    return Err(InconsistentNeuronError::DuplicateSample(row.sample_id));
                }
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
    /// If `validate_order` is `false`, samples may be defined earlier in the file than their parents.
    pub fn validate(&self, validate_order: bool) -> Result<(), InconsistentNeuronError> {
        use InconsistentNeuronError::*;

        // use sample IDs
        let mut parent_to_children: HashMap<SampleId, Vec<SampleId>> =
            HashMap::with_capacity(self.samples.len());
        let mut sample_ids: HashSet<SampleId> = HashSet::with_capacity(self.samples.len());
        let mut root = None;

        for row in self.samples.iter() {
            if !sample_ids.insert(row.sample_id) {
                return Err(DuplicateSample(row.sample_id));
            }
            if let Some(p) = row.parent_id {
                if validate_order && !sample_ids.contains(&p) {
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
    pub fn from_reader<R: BufRead>(reader: R) -> Result<Self, SwcParseError> {
        SwcLines::<S, R>::new(reader)?.try_into()
    }

    /// Dump this [SwcNeuron] to a [Write]r.
    ///
    /// These writes are quite small: consider wrapping it in a [BufWriter].
    pub fn to_writer<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        if let Some(h) = self.header.clone() {
            for line in h.to_string().lines() {
                writeln!(writer, "#{}", line)?;
            }
        }
        for s in self.samples.iter() {
            writeln!(writer, "{}", s)?;
        }
        Ok(())
    }

    /// Replace the existing header with a new one, returning the existing.
    pub fn replace_header(&mut self, header: Option<H>) -> Option<H> {
        std::mem::replace(&mut self.header, header)
    }

    /// Create a new header by applying a function to this [SwcNeuron],
    /// then create a new neuron with that header.
    pub fn try_map_header<H2: Header, E: Error, F: Fn(&Self) -> Result<Option<H2>, E>>(
        self,
        f: F,
    ) -> Result<SwcNeuron<S, H2>, E> {
        let header = f(&self)?;
        Ok(SwcNeuron {
            header,
            samples: self.samples,
        })
    }

    /// Map every sample's structure to another type.
    pub fn try_map_structure<S2: StructureIdentifier, E: Error, F: Fn(&S) -> Result<S2, E>>(
        self,
        f: F,
    ) -> Result<SwcNeuron<S2, H>, E> {
        let samples: Result<Vec<_>, E> = self
            .samples
            .into_iter()
            .map(|s| {
                Ok(SwcSample {
                    sample_id: s.sample_id,
                    structure: f(&s.structure)?,
                    x: s.x,
                    y: s.y,
                    z: s.z,
                    radius: s.radius,
                    parent_id: s.parent_id,
                })
            })
            .collect();
        Ok(SwcNeuron {
            samples: samples?,
            header: self.header,
        })
    }

    /// Get the highest sample ID in the neuron, if any samples exist.
    pub fn max_idx(&self) -> Option<SampleId> {
        self.samples.iter().map(|s| s.sample_id).max()
    }
}

impl<S: StructureIdentifier, H: Header, R: BufRead> TryFrom<SwcLines<S, R>> for SwcNeuron<S, H> {
    type Error = SwcParseError;

    fn try_from(mut lines: SwcLines<S, R>) -> Result<Self, Self::Error> {
        let header: Option<H> = if let Some(h_res) = lines.header() {
            let h = h_res.map_err(|_e| SwcParseError::HeaderParse(lines.header_string.clone()))?;
            Some(h)
        } else {
            None
        };

        let mut samples = Vec::default();
        for ln_res in lines {
            match ln_res? {
                SwcLine::Comment(_) => (),
                SwcLine::Sample(s) => samples.push(s),
            }
        }
        Ok(Self { samples, header })
    }
}

/// [Iterator] which eagerly reads the header on construction and then lazily reads the remaining lines.
pub struct SwcLines<S: StructureIdentifier, R: BufRead> {
    inner: SwcFileLines<S, R>,
    header_string: String,
    next_row: Option<<SwcFileLines<S, R> as Iterator>::Item>,
}

impl<S: StructureIdentifier, R: BufRead> SwcLines<S, R> {
    /// Create a new [SwcLines] iterator from a reader.
    pub fn new(reader: R) -> Result<Self, io::Error> {
        let mut inner = SwcFileLines::new(reader);
        let mut header_string = String::with_capacity(HEADER_BUF_LEN);
        let mut next_row = None;

        loop {
            let Some(ln) = inner.next() else {
                break;
            };
            match ln {
                Ok(SwcLine::Comment(c)) => {
                    header_string.push('\n');
                    header_string.push_str(&c);
                }
                _ => {
                    next_row = Some(ln);
                    break;
                }
            }
        }

        Ok(Self {
            inner,
            header_string,
            next_row,
        })
    }

    /// Parse the header string into a [Header] struct.
    pub fn header<H: Header>(&mut self) -> Option<Result<H, <H as std::str::FromStr>::Err>> {
        if self.header_string.is_empty() {
            None
        } else {
            Some(self.header_string.parse::<H>())
        }
    }
}

impl<S: StructureIdentifier, R: BufRead> Iterator for SwcLines<S, R> {
    type Item = Result<SwcLine<S>, SwcParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(o) = self.next_row.take() {
            return Some(o);
        }
        self.inner.next()
    }
}

/// Line in a SWC file, which might be a comment or sample.
pub enum SwcLine<S: StructureIdentifier> {
    /// Comment line, which may be part of the header
    Comment(String),
    /// Sample line
    Sample(SwcSample<S>),
}

/// [Iterator] which produces [SwcLine]s from a [Read]er.
struct SwcFileLines<S: StructureIdentifier, R: BufRead> {
    lines: Lines<R>,
    pub is_header: bool,
    _s: PhantomData<S>,
}

impl<S: StructureIdentifier, R: BufRead> SwcFileLines<S, R> {
    fn new(reader: R) -> Self {
        Self {
            lines: reader.lines(),
            is_header: true,
            _s: PhantomData,
        }
    }
}

impl<S: StructureIdentifier, R: BufRead> Iterator for SwcFileLines<S, R> {
    type Item = Result<SwcLine<S>, SwcParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let raw_line = match self.lines.next()? {
                Ok(s) => s,
                Err(e) => return Some(Err(SwcParseError::Read(e))),
            };

            let line = raw_line.trim_end();

            if line.is_empty() {
                continue;
            } else if let Some(remainder) = line.strip_prefix('#') {
                return Some(Ok(SwcLine::Comment(remainder.to_string())));
            } else {
                return match SwcSample::from_str(line) {
                    Ok(sample) => {
                        self.is_header = false;
                        Some(Ok(SwcLine::Sample(sample)))
                    }
                    Err(err) => Some(Err(SwcParseError::SampleParse(err))),
                };
            }
        }
    }
}

/// Parse lines from a SWC file.
///
/// Skips blank lines and treats all `#`-prefixed lines as comments.
/// Does not check the neuron for consistency, but does check for valid structures.
pub fn parse_swc_lines<R: BufRead, S: StructureIdentifier>(
    reader: R,
) -> impl Iterator<Item = Result<SwcLine<S>, SwcParseError>> {
    SwcFileLines::new(reader)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{read_dir, File};
    use std::io::BufReader;
    use std::path::PathBuf;

    fn data_dir() -> PathBuf {
        let mut p = PathBuf::from_str(env!("CARGO_MANIFEST_DIR")).unwrap();
        p.push("data");
        p
    }

    fn data_paths() -> impl IntoIterator<Item = PathBuf> {
        let root = data_dir();
        read_dir(&root).unwrap().filter_map(|er| {
            let e = er.unwrap();
            let p = e.path();
            if p.is_file() && p.ends_with(".swc") {
                Some(p)
            } else {
                None
            }
        })
    }

    fn all_swcs() -> impl IntoIterator<Item = AnySwc> {
        data_paths().into_iter().map(|p| {
            let f = File::open(&p).unwrap();
            AnySwc::from_reader(BufReader::new(f))
                .unwrap_or_else(|_| panic!("Could not read {:?}", p.as_os_str()))
        })
    }

    #[test]
    fn can_read() {
        for s in all_swcs() {
            assert!(matches!(s.header, Some(h) if !h.is_empty()));
            assert!(!s.samples.is_empty());
        }
    }

    #[test]
    fn can_validate() {
        for swc in all_swcs() {
            swc.validate(true).expect("Invalid SWC");
        }
    }
}
