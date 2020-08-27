use std::convert::TryFrom;
use std::fmt::Debug;

pub trait StructureIdentifier: Copy + Clone + Debug + TryFrom<isize> + Into<isize> {}

#[macro_export]
macro_rules! structure_mapping {
    ( $id:ident $(, $val:literal = $name:ident )* $(,)?) => {
        #[derive(Copy, Clone, Debug)]
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

        impl Into<isize> for $id {
            fn into(self) -> isize {
                match self {
                    $( Self::$name => $val, )*
                }
            }
        }

        impl StructureIdentifier for $id {}

    };
    ( $id:ident $(, $val:literal = $name:ident )*, $othername:ident $(,)?) => {
        #[derive(Copy, Clone, Debug)]
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

        impl Into<isize> for $id {
            fn into(self) -> isize {
                match self {
                    $( Self::$name => $val, )*
                    Self::$othername(x) => x,
                }
            }
        }

        impl StructureIdentifier for $id {}

    };
}

#[macro_export]
macro_rules! neuromorpho_ext {
    ( $id:ident $(, $val:literal = $name:ident )* $(,)?) => {
        structure_mapping!(
            $id,
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
neuromorpho_ext!(VnedStructure, 10 = SomaRelated, Custom);

structure_mapping!(GulyasStructure, IsoDiameterStructure);
