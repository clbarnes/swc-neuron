//! Module for types represented by the structure ID field of a SWC sample.
//!
//! Contains some known structure schemas and macros for creating more.
use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt::Debug;

/// Trait for the structures represented by samples, identified by an integer.
pub trait StructureIdentifier: Copy + Clone + Debug + TryFrom<isize> + Into<isize> {
    /// List all the variants which are not catch-alls.
    fn known_variants() -> &'static[Self];

    /// If the structure field allows for any value, return `None`;
    /// otherwise, return `Some(HashSet<allowed_values>)`.
    /// `no_catchall`, if `true`, ignores the "catch-all" variant
    /// in determining what is allowed, if present.
    fn allowed_values(no_catchall: bool) -> Option<HashSet<isize>>;

    /// Get a static string description of the structure; None if this is the catch-all variant.
    fn as_str(&self) -> Option<&'static str>;
}

/// Macro for creating a public enum implementing StructureIdentifier.
///
/// The first argument is the enum's identifier.
/// Subsequent arguments are given in the form `value = variant "longer name"`:
/// that is, a signed integer literal, then an equals sign, then
/// the identifier of the enum variant that literal represents,
/// then a string literal describing the variant.
/// There is an optional final argument which is the identifier of a variant
/// which catches all other values, and stores the value originally given to it.
///
/// If the final argument is given, the enum implements From<isize>:
/// otherwise, it only implements TryFrom<isize>,
/// returning an error which contains the offending integer.
#[macro_export]
macro_rules! structure_mapping {
    ( $id:ident $(, $val:literal = $name:ident $desc:expr )* $(,)?) => {
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
            fn known_variants() -> &'static [Self] {
                &[
                    $( Self::$name, )*
                ]
            }

            fn allowed_values(_no_catchall: bool) -> Option<HashSet<isize>> {
                Some(vec![$( $val, )*].into_iter().collect())
            }

            fn as_str(&self) -> Option<&'static str> {
                match self {
                    $( Self::$name => Some($desc), )*
                }
            }
        }

    };
    ( $id:ident $(, $val:literal = $name:ident $desc:expr )*, $othername:ident $(,)?) => {
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
            fn known_variants() -> &'static [Self] {
                &[
                    $( Self::$name, )*
                ]
            }

            fn allowed_values(no_catchall: bool) -> Option<HashSet<isize>> {
                if no_catchall {
                    Some(vec![$( $val, )*].into_iter().collect())
                } else {
                    None
                }
            }

            fn as_str(&self) -> Option<&'static str> {
                match self {
                    $( Self::$name => Some($desc), )*
                    Self::$othername(_) => None,
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
    ( $id:ident $(, $val:literal = $name:ident $desc:expr )* $(,)?) => {
        structure_mapping!(
            $id,
            -1 = Root "root",
            0 = Undefined "undefined",
            1 = Soma "soma",
            2 = Axon "axon",
            3 = BasalDendrite "basal dendrite",
            4 = ApicalDendrite "apical dendrite",
            $($val = $name $desc, )*
        );
    };
    ( $id:ident $(, $val:literal = $name:ident $desc:expr )*, $othername:ident $(,)?) => {
        structure_mapping!(
            $id,
            -1 = Root "root",
            0 = Undefined "undefined",
            1 = Soma "soma",
            2 = Axon "axon",
            3 = BasalDendrite "basal dendrite",
            4 = ApicalDendrite "apical dendrite",
            $($val = $name $desc, )*
            $othername,
        );
    };
}

neuromorpho_ext!(NeuromorphoStructure, Custom);
neuromorpho_ext!(CnicStructure, 5 = ForkPoint "fork point", 6 = EndPoint "end point", 7 = Custom "custom");
neuromorpho_ext!(
    NavisStructure,
    5 = ForkPoint "fork point",
    6 = EndPoint "end point",
    7 = Presynapse "presynapse",
    8 = Postsynapse "postsynapse",
    9 = PreAndPostsynapse "pre and postsynapse",
    Custom,
);
neuromorpho_ext!(VnedStructure, 10 = SomaRelated "soma related", Custom);

structure_mapping!(GulyasStructure, IsoDiameterStructure);
structure_mapping!(AnyStructure, Any);
