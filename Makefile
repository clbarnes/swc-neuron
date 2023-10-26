readme:
	cargo run --all-features -- --help | pipe2codeblock README.md --tgt _swctool
