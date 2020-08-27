use std::fmt::Debug;
use std::io::{BufReader, BufRead, Read, Write};
use std::iter::FromIterator;
use std::str::FromStr;

mod structures;

pub use crate::structures::{
    CnicStructure, GulyasStructure, NeuromorphoStructure, StructureIdentifier, VnedStructure,
};

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

#[derive(Debug, Clone)]
pub struct SwcSample<T: StructureIdentifier> {
    pub sample: usize,
    pub structure: T,
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub radius: f64,
    pub parent: Option<usize>,
}

impl<T: StructureIdentifier> FromStr for SwcSample<T> {
    type Err = SampleParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed = s.trim();
        let mut items = trimmed.split_whitespace();

        let sample  = items.next().ok_or(SampleParseError::IncorrectNumFields(0))?.parse()?;

        let struct_int = items.next().ok_or(SampleParseError::IncorrectNumFields(1))?.parse::<isize>()?;
        let structure = T::try_from(struct_int).map_err(|_e| SampleParseError::UnknownStructure(struct_int))?;
        let x = items.next().ok_or(SampleParseError::IncorrectNumFields(2))?.parse::<f64>()?;
        let y = items.next().ok_or(SampleParseError::IncorrectNumFields(3))?.parse::<f64>()?;
        let z = items.next().ok_or(SampleParseError::IncorrectNumFields(4))?.parse::<f64>()?;
        let radius = items.next().ok_or(SampleParseError::IncorrectNumFields(5))?.parse::<f64>()?;
        let parent = match items.next() {
            Some(p_str) => Some(p_str.parse()?),
            None => None,
        };

        return Ok(Self {
            sample,
            structure,
            x,
            y,
            z,
            radius,
            parent,
        });

    }
}

impl<T: StructureIdentifier> ToString for SwcSample<T> {
    fn to_string(&self) -> String {
        let structure: isize = self.structure.into();
        let mut s = format!("{} {} {} {} {} {}", self.sample, structure, self.x, self.y, self.z, self.radius);
        if let Some(p) = self.parent {
            s = format!("{} {}", s, p)
        }
        return s
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
    ReadError(std::io::Error),
    #[error("Sample parse error")]
    SampleParseError(#[from] SampleParseError),
}

impl<T: StructureIdentifier> SwcNeuron<T> {
    pub fn from_reader<R: Read>(reader: R) -> Result<Self, SwcParseError> {
        let buf = BufReader::new(reader);

        let mut samples = Vec::default();
        for result in buf.lines() {
            let line = result.map_err(|e| SwcParseError::ReadError(e))?;
            if line.starts_with("#") {
                continue;
            }
            let sample: SwcSample<T> = match SwcSample::from_str(&line) {
                Err(SampleParseError::IncorrectNumFields(0)) => continue,
                other => other,
            }?;
            samples.push(sample);
        }

        return Ok(Self { samples });
    }

    pub fn to_writer<W: Write>(&self, writer: &mut W) -> Result<(), std::io::Error> {
        for s in self.samples.iter() {
            writeln!(writer, "{}", s.to_string())?;
        }
        Ok(())
    }
}
