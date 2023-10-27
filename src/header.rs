//! Module for metadata contained in the header of the SWC file.
use std::{fmt::Debug, str::FromStr};

/// Trait for metadata which can be read and written from a block comment at the head of the file.
pub trait Header: Clone + Debug + ToString + FromStr {}

impl Header for String {}
