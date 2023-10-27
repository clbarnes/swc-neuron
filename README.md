# swc-neuron

Rust library for reading, writing, and manipulating SWC files for neuronal morphology.
Also includes a CLI for basic validation, sorting, and reindexing (with optional feature `cli`).

The format was originally proposed in [Cannon, et al. 1998](http://dx.doi.org/10.1016/S0165-0270(98)00091-0),
with an implementation in [dohalloran/SWC_BATCH_CHECK](https://github.com/dohalloran/SWC_BATCH_CHECK).

While commonly used, many variants exist; this implementation tries to cover the "standardised" version described
[here](http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html),
with some ambiguities resolved by the [SWCplus specification](https://neuroinformatics.nl/swcPlus/).

The header is a series of `#`-prefixed lines starting at the beginning of the file.
Blank lines (i.e. without a `#` or any other non-whitespace content) do not interrupt the header,
but are also not included in the parsed header.
The `SwcNeuron` type is generic over implementors of `Header`,
which is currently only implemented for `String`
(i.e. it is treated as a free text field, with the leading `#` on each line removed).
All other `#`-prefixed and all whitespace-only lines in the file after the first sample are ignored.

## swctool

```_swctool
swctool 0.2.1
Tool for manipulating and validating SWC neuronal morphology files.

Implementation is based on the "specification" at
http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html

All headers, blank lines, and whitespace separators other than a single space character between each field will be
removed.

USAGE:
    swctool [FLAGS] [OPTIONS] [ARGS]

FLAGS:
    -h, --help           
            Prints help information

    -n, --no-catchall    
            Some known sub-specifications have a "catch-all" structure which allows any value to be valid: this argument
            ignores that structure if "structures" is given
    -r, --reindex        
            Reindex the samples, starting at 1 (happens after sorting)

    -s, --sort           
            Sort the samples by their sample number (happens before reindexing)

    -t, --toposort       
            Sort the samples topologically in depth first preorder from the root; must be a valid tree

    -u, --unordered      
            If using --validate, allow samples to be given out of order (i.e. parents can be defined after their
            children). Ignored if --validate is not given
    -V, --validate       
            Check that SWC describes a valid tree. --toposort requires a valid tree structure

        --version        
            Prints version information


OPTIONS:
    -S, --structures <structures>    
            If given, structure IDs will be checked against the given comma-separated list of integers. Also accepts the
            names of known SWC sub-specifications: "neuromorpho", "cnic", "vned", "gulyas", "navis". If your schema
            extends a known sub-spec, give e.g. "cnic,8,9,10"

ARGS:
    <input>     
            Input file; does nothing if not given, reads from stdin if -

    <output>    
            Output file; writes nothing if not given, writes to stdout if -

```

## Example data

Provided by neuromorpho.org. Some are standardised, some are not.

## Notes on SWC headers

"Standard" SWC (as originally proposed) has some particular metadata fields which "should" exist in the header.
Neuromorpho SWC has no header requirements.
SWCplus encodes more complex metadata as XML in the header.

Note that the SWCplus specification web page has some encoding issues.
In the metadata, the separator between the last name and initials of `CONTRIBUTOR` should be an underscore `_`,
and the `SOMA_AREA` should be in square micrometers `μm²`, not square millimeters `mm²`.

## Development

Release tags etc. should be handled by cargo-release; the release itself is then made on CI.
