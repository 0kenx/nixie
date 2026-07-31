//! Benchmark prediction accuracy

// Benches are test-class code: panicking on broken setup is the desired
// failure mode, but clippy has no allow-unwrap-in-benches analogue to the
// allow-unwrap-in-tests knob that covers the test targets.
#![allow(clippy::unwrap_used)]
use criterion::{Criterion, criterion_group, criterion_main};
use oxiz_ml::models::{LinearRegression, Model, NeuralNetwork};
use std::hint::black_box;

fn benchmark_neural_network_predict(c: &mut Criterion) {
    let network = NeuralNetwork::simple(vec![10, 8, 4, 1]).unwrap();
    let input = vec![0.5; 10];

    c.bench_function("neural_network_predict", |b| {
        b.iter(|| network.predict(black_box(&input)));
    });
}

fn benchmark_linear_model_predict(c: &mut Criterion) {
    let model = LinearRegression::new(10);
    let input = vec![0.5; 10];

    c.bench_function("linear_model_predict", |b| {
        b.iter(|| model.predict(black_box(&input)));
    });
}

criterion_group!(
    benches,
    benchmark_neural_network_predict,
    benchmark_linear_model_predict
);
criterion_main!(benches);
