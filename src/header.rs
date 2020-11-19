use std::{fmt::Debug, str::FromStr};

pub trait Header: Clone + Debug + ToString + FromStr {}

impl Header for String {}
