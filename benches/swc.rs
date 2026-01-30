use criterion::{black_box, criterion_group, criterion_main, Criterion};
use swc_neuron::AnySwc;

use std::collections::HashMap;
use std::fs::{read_dir, File};
use std::io::{BufReader, Read};
use std::path::PathBuf;
use std::str::FromStr;

fn data_dir() -> PathBuf {
    let mut p = PathBuf::from_str(env!("CARGO_MANIFEST_DIR")).unwrap();
    p.push("data");
    p
}

fn data_paths() -> impl IntoIterator<Item = PathBuf> {
    let root = data_dir();
    read_dir(&root).unwrap().filter_map(|er| {
        let e = er.unwrap();
        let p = e.path();
        if p.is_file() && p.ends_with(".swc") {
            Some(p)
        } else {
            None
        }
    })
}

fn preload_data() -> HashMap<String, Vec<u8>> {
    data_paths()
        .into_iter()
        .map(|p| {
            let fname = p.file_name().unwrap().to_string_lossy().to_string();
            let mut f = BufReader::new(File::open(&p).unwrap());
            let mut buf = Vec::default();
            f.read_to_end(&mut buf).unwrap();
            (fname, buf)
        })
        .collect()
}

fn preload_swcs() -> HashMap<String, AnySwc> {
    preload_data()
        .into_iter()
        .map(|(name, buf)| (name, AnySwc::from_reader(buf.as_slice()).unwrap()))
        .collect()
}

pub fn bench_parse(c: &mut Criterion) {
    let data = preload_data();
    c.bench_function("parse", |b| {
        b.iter(|| {
            let _swcs: Vec<_> = data
                .values()
                .map(|buf| {
                    let swc = AnySwc::from_reader(black_box(buf.as_slice())).unwrap();
                    assert!(!swc.is_empty());
                    swc
                })
                .collect();
        })
    });
}

pub fn bench_toposort(c: &mut Criterion) {
    let swcs = preload_swcs();
    c.bench_function("toposort", |b| {
        b.iter(|| {
            let swcs2 = swcs.clone();
            swcs2.into_values().for_each(|swc| {
                swc.sort_topo(true).unwrap();
            });
        })
    });
}

criterion_group!(benches, bench_parse, bench_toposort);
criterion_main!(benches);
