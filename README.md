# swc-neuron

Rust library for reading, writing, and manipulating SWC files for neuronal morphology.
Also includes a CLI for basic validation, sorting, and reindexing.

The format was originally proposed in [Cannon, et al. 1998](http://dx.doi.org/10.1016/S0165-0270(98)00091-0).

While commonly used, many variants exist; this implementation tries to cover the "standardised" version described
[here](http://www.neuronland.org/NLMorphologyConverter/MorphologyFormats/SWC/Spec.html).

The header is an uninterrupted series of commented lines starting at the beginning of the file.
The `SwcNeuron` type is generic over implementors of `Header`,
which is currently only implemented for `String` (i.e. it is treated as a free text field).
All other `#`-prefixed or whitespace-only lines are ignored.

A more strictly specified and greatly expanded specification for "SWC+" also exists [here](https://neuroinformatics.nl/swcPlus/).
