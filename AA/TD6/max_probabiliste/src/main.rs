#![warn(clippy::all)]

use rand::{thread_rng, Rng};
use rayon::prelude::*;
use std::iter::repeat_with;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

// renvoie si l'indiceieme element de la tranche est son max.
// D = O(1)
// W = O(n)
fn est_max(tranche: &[usize], indice: usize) -> bool {
    let encore_max = AtomicBool::new(true);
    (0..tranche.len()).into_par_iter().for_each(|i| {
        if i != indice && tranche[i] > tranche[indice] {
            encore_max.store(false, Ordering::SeqCst)
        }
    });
    encore_max.load(Ordering::SeqCst)
}

fn max_ultra_rapide(tranche: &[usize]) -> usize {
    let indice_max = AtomicUsize::new(0);
    (0..tranche.len()).into_par_iter().for_each(|i| {
        if est_max(tranche, i) {
            indice_max.store(i, Ordering::SeqCst)
        }
    });
    tranche[indice_max.load(Ordering::SeqCst)]
}

fn max_vegas(tranche: &[usize]) -> usize {
    let taille = (tranche.len() as f64).sqrt().ceil() as usize;
    let echantillon: Vec<_> = (0..taille)
        .into_par_iter()
        .map(|_| {
            let mut rng = thread_rng();
            *rng.choose(tranche).unwrap()
        })
        .collect();

    let faux_max = max_ultra_rapide(&echantillon);

    let reste: Vec<_> = tranche
        .par_iter()
        .filter(|&x| *x >= faux_max)
        .cloned()
        .collect();

    max_ultra_rapide(&reste)
}

fn max_monte_carlo(tranche: &[usize]) -> usize {
    let taille = (tranche.len() as f64).sqrt().ceil() as usize;
    let echantillon: Vec<_> = (0..taille)
        .into_par_iter()
        .map(|_| {
            let mut rng = thread_rng();
            *rng.choose(tranche).unwrap()
        })
        .collect();

    let faux_max = max_ultra_rapide(&echantillon);

    let reste: Vec<_> = (0..(2 * taille))
        .into_par_iter()
        .map(|_| AtomicUsize::new(std::usize::MIN))
        .collect();

    tranche
        .par_iter()
        .filter(|&x| *x >= faux_max)
        .for_each(|x| {
            let mut rng = thread_rng();
            rng.choose(&reste).unwrap().store(*x, Ordering::SeqCst);
        });

    let reste_entier: Vec<_> = reste.par_iter().map(|e| e.load(Ordering::SeqCst)).collect();

    max_ultra_rapide(&reste_entier)
}

fn main() {
    let mut v: Vec<_> = (0..10_000).collect();
    let max = v.last().cloned().unwrap();
    let mut rng = thread_rng();
    rng.shuffle(&mut v);
    assert_eq!(max, max_ultra_rapide(&v));
    assert_eq!(max, max_vegas(&v));
    let proba = repeat_with(|| max_monte_carlo(&v))
        .take(1000)
        .filter(|&m| m == max)
        .count() as f64
        / 1000.0;
    println!(
        "l'algorithme de monte carlo a une probabilite de {} de reussir",
        proba
    );
}
