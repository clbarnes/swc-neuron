use std::collections::HashSet;
use std::fs;
use std::io::{self, BufReader, BufWriter, Write};
use std::path::PathBuf;

use structopt::StructOpt;

use swc_neuron::structures::{
    CnicStructure, GulyasStructure, NavisStructure, NeuromorphoStructure, VnedStructure,
};
use swc_neuron::{AnySwc, Header, StructureIdentifier, SwcNeuron};

#[derive(Debug, StructOpt)]
#[structopt(name = "swctool")]
/// Tool for manipulating and validating SWC neuronal morphology files.
///
/// Implementation is based on the "specification" at
/// http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html
///
/// All headers, blank lines, and whitespace separators other than a single space character between each field will be removed.
struct Opt {
    /// Sort the samples topologically in depth first preorder from the root; must be a valid tree
    #[structopt(short, long)]
    toposort: bool,

    /// Check that SWC describes a valid tree. --toposort requires a valid tree structure.
    #[structopt(short = "V", long)]
    validate: bool,

    /// If using --validate, allow samples to be given out of order (i.e. parents can be defined after their children).
    /// Ignored if --validate is not given.
    #[structopt(short = "u", long)]
    unordered: bool,

    /// Sort the samples by their sample number (happens before reindexing)
    #[structopt(short, long)]
    sort: bool,

    /// Reindex the samples, starting at 1 (happens after sorting)
    #[structopt(short, long)]
    reindex: bool,

    /// If given, structure IDs will be checked against the given comma-separated list of integers.
    /// Also accepts the names of known SWC sub-specifications: "neuromorpho", "cnic", "vned", "gulyas", "navis".
    /// If your schema extends a known sub-spec, give e.g. "cnic,8,9,10"
    #[structopt(short = "S", long)]
    structures: Option<String>,

    /// Some known sub-specifications have a "catch-all" structure which allows any value to be valid:
    /// this argument ignores that structure if "structures" is given
    #[structopt(short, long)]
    no_catchall: bool,

    /// Input file; does nothing if not given, reads from stdin if -
    #[structopt(parse(from_os_str))]
    input: Option<PathBuf>,

    /// Output file; writes nothing if not given, writes to stdout if -
    #[structopt(parse(from_os_str))]
    output: Option<PathBuf>,
}

fn parse_structures(input: &str, no_catchall: bool) -> anyhow::Result<Option<HashSet<isize>>> {
    let mut elements = input.split(',');
    let first_opt = elements.next();
    if first_opt.is_none() {
        return Ok(Some(HashSet::with_capacity(0)));
    }
    let vals: Option<HashSet<isize>> = match &first_opt.unwrap().to_lowercase()[..] {
        "cnic" => CnicStructure::allowed_values(no_catchall),
        "neuromorpho" => NeuromorphoStructure::allowed_values(no_catchall),
        "vned" => VnedStructure::allowed_values(no_catchall),
        "gulyas" => GulyasStructure::allowed_values(no_catchall),
        "navis" => NavisStructure::allowed_values(no_catchall),
        n => Some(vec![n.parse()?].into_iter().collect()),
    };

    if let Some(mut v) = vals {
        for el in elements {
            v.insert(el.parse()?);
        }
        Ok(Some(v))
    } else {
        Ok(None)
    }
}

fn bad_structures<S: StructureIdentifier, H: Header>(
    allowed: &HashSet<isize>,
    neuron: &SwcNeuron<S, H>,
) -> HashSet<isize> {
    let mut out = HashSet::default();
    for row in neuron.samples.iter() {
        let val = row.structure.into();
        if !allowed.contains(&val) {
            out.insert(val);
        }
    }
    out
}

fn read<S: StructureIdentifier, H: Header>(input: PathBuf) -> anyhow::Result<SwcNeuron<S, H>> {
    if input == PathBuf::from("-") {
        Ok(SwcNeuron::from_reader(BufReader::new(io::stdin()))?)
    } else {
        Ok(SwcNeuron::from_reader(BufReader::new(fs::File::open(
            input,
        )?))?)
    }
}

fn write<S: StructureIdentifier, H: Header>(
    output: Option<PathBuf>,
    neuron: SwcNeuron<S, H>,
) -> anyhow::Result<()> {
    if let Some(p) = output {
        if p == PathBuf::from("-") {
            neuron.to_writer(&mut BufWriter::new(io::stdout()))?;
        } else {
            neuron.to_writer(&mut BufWriter::new(fs::File::create(p)?))?;
        }
    }

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let opt = Opt::from_args();
    if opt.input.is_none() {
        io::stderr().write_all(b"No input file given, nothing to do\n")?;
        return Ok(());
    }
    let input = opt.input.unwrap();
    let mut nrn: AnySwc = read(input)?;

    if let Some(s) = opt.structures {
        let allowed = parse_structures(&s[..], opt.no_catchall)?;
        if let Some(a) = allowed {
            let bad = bad_structures(&a, &nrn);
            if !bad.is_empty() {
                anyhow::bail!("Found {} unspecified structures: {:?}", bad.len(), bad);
            }
        }
    }

    if opt.toposort {
        // implicitly sorts, validates; explicitly reindexes
        let sorted = nrn.sort_topo(opt.reindex)?;
        return write(opt.output, sorted);
    }

    // reindex -> sort would make the sort superfluous
    if opt.sort {
        nrn = nrn.sort_index();
    }
    if opt.reindex {
        nrn = nrn.reindex()?;
    }
    if opt.validate {
        nrn.validate(opt.unordered)?;
    }

    write(opt.output, nrn)
}
