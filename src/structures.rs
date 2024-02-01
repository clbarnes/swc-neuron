//! Module for types represented by the structure ID field of a SWC sample.
//!
//! Contains some known structure schemas and macros for creating more.
use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt::Debug;

/// Trait for the structures represented by samples, identified by an integer.
pub trait StructureIdentifier: Copy + Clone + Debug + TryFrom<isize> + Into<isize> {
    /// If the structure field allows for any value, return `None`;
    /// otherwise, return `Some(HashSet<allowed_values>)`.
    /// `no_catchall`, if `true`, ignores the "catch-all" variant
    /// in determining what is allowed, if present.
    fn allowed_values(no_catchall: bool) -> Option<HashSet<isize>>;
}

/// Macro for creating a public enum implementing StructureIdentifier.
///
/// The first argument is the enum's identifier.
/// Subsequent arguments are given in the form `value = variant`:
/// that is, a signed integer literal, then an equals sign, then
/// the identifier of the enum variant that literal represents.
/// There is an optional final argument which is the identifier of a variant
/// which catches all other values, and stores the value originally given to it.
///
/// If the final argument is given, the enum implements From<isize>:
/// otherwise, it only implements TryFrom<isize>,
/// returning an error which contains the offending integer.
#[macro_export]
macro_rules! structure_mapping {
    ( $id:ident $(, $val:literal = $name:ident )* $(,)?) => {
        #[derive(Copy, Clone, Debug)]
        #[allow(missing_docs)]
        pub enum $id {
            $( $name, )+
        }

        impl TryFrom<isize> for $id {
            type Error = isize;

            fn try_from(val: isize) -> Result<Self, Self::Error> {
                match val {
                    $( $val => Ok(Self::$name), )*
                    value => Err(value),
                }
            }
        }

        impl From<$id> for isize {
            fn from(val: $id) -> Self {
                match val {
                    $( $id::$name => $val, )*
                }
            }
        }

        impl StructureIdentifier for $id {
            fn allowed_values(_no_catchall: bool) -> Option<HashSet<isize>> {
                Some(vec![$( $val, )*].into_iter().collect())
            }
        }

    };
    ( $id:ident $(, $val:literal = $name:ident )*, $othername:ident $(,)?) => {
        #[derive(Copy, Clone, Debug)]
        #[allow(missing_docs)]
        pub enum $id {
            $( $name, )*
            $othername(isize),
        }

        impl From<isize> for $id {
            fn from(val: isize) -> Self {
                match val {
                    $( $val => Self::$name, )*
                    x => Self::$othername(x),
                }
            }
        }

        impl From<$id> for isize {
            fn from(val: $id) -> Self {
                match val {
                    $( $id::$name => $val, )*
                    $id::$othername(x) => x,
                }
            }
        }

        impl StructureIdentifier for $id {
            fn allowed_values(no_catchall: bool) -> Option<HashSet<isize>> {
                if no_catchall {
                    Some(vec![$( $val, )*].into_iter().collect())
                } else {
                    None
                }
            }
        }

    };
}

/// Thin wrapper around the `structure_mapping` macro for producing enums
/// which extend the Neuromorpho SWC standard (i.e. have additional structure types in the `Custom` block, 5+).
///
/// Again, you can either allow or disallow the catch-all case.
#[macro_export]
macro_rules! neuromorpho_ext {
    ( $id:ident $(, $val:literal = $name:ident )* $(,)?) => {
        structure_mapping!(
            $id,
            -1 = Root,
            0 = Undefined,
            1 = Soma,
            2 = Axon,
            3 = BasalDendrite,
            4 = ApicalDendrite,
            $($val = $name, )*
        );
    };
    ( $id:ident $(, $val:literal = $name:ident )*, $othername:ident $(,)?) => {
        structure_mapping!(
            $id,
            -1 = Root,
            0 = Undefined,
            1 = Soma,
            2 = Axon,
            3 = BasalDendrite,
            4 = ApicalDendrite,
            $($val = $name, )*
            $othername,
        );
    };
}

neuromorpho_ext!(NeuromorphoStructure, Custom);
neuromorpho_ext!(CnicStructure, 5 = ForkPoint, 6 = EndPoint, 7 = Custom);
neuromorpho_ext!(
    NavisStructure,
    5 = ForkPoint,
    6 = EndPoint,
    7 = Presynapse,
    8 = Postsynapse,
    9 = PreAndPostsynapse,
    Custom,
);
neuromorpho_ext!(VnedStructure, 10 = SomaRelated, Custom);

structure_mapping!(GulyasStructure, IsoDiameterStructure);
structure_mapping!(AnyStructure, Any);
