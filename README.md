# swc-neuron

Rust library for reading, writing, and manipulating SWC files for neuronal morphology.
Also includes a CLI for basic validation, sorting, and reindexing.

The format was originally proposed in [Cannon, et al. 1998](http://dx.doi.org/10.1016/S0165-0270(98)00091-0),
with an implementation in [dohalloran/SWC_BATCH_CHECK](https://github.com/dohalloran/SWC_BATCH_CHECK).

While commonly used, many variants exist; this implementation tries to cover the "standardised" version described
[here](http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html),
with some ambiguities resolved by the [SWCplus specification](https://neuroinformatics.nl/swcPlus/).

The header is an uninterrupted series of `#`-prefixed lines starting at the beginning of the file.
The `SwcNeuron` type is generic over implementors of `Header`,
which is currently only implemented for `String`
(i.e. it is treated as a free text field, with the first `#` and leading whitespace stripped).
All other `#`-prefixed and all whitespace-only lines are ignored.

"Standard" SWC (as originally proposed) has some particular metadata fields which "should" exist in the header.
Neuromorpho SWC has no header requirements.
SWCplus encodes more complex metadata as XML in the header.

Note that the SWCplus specification web page has some encoding issues.
In the metadata, the separator between the last name and initials of `CONTRIBUTOR` should be an underscore `_`,
and the `SOMA_AREA` should be in square micrometers `μm²`, not square millimeters `mm²`.

## swctool

```_swctool
swctool 0.1.1
Tool for manipulating and validating SWC neuronal morphology files.

Implementation is based on the "specification" at
http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html

All headers, blank lines, and whitespace separators other than a single space character will be removed.

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
            Check that SWC describes a valid tree. --toposort also will also validate the tree structure

        --version        
            Prints version information


OPTIONS:
    -S, --structures <structures>    
            If given, structure IDs will be checked against the given comma-separated list. Also accepts the names of
            known SWC sub-specifications: "neuromorpho", "cnic", "vned", "gulyas". If your schema extends a known sub-
            spec, give e.g. "cnic,8,9,10"

ARGS:
    <input>     
            Input file; reads from stdin if -

    <output>    
            Output file; writes to stdout if empty or -

```

## Example data

Provided by neuromorpho.org. Some are standardised, some are not.
