#![warn(clippy::all)]
use rayon::prelude::*;

const N: usize = 10;

fn produit_matrice_vecteur(m: &[[u32; N]; N], v: &[u32; N]) -> [u32; N] {
    let mut r = [0; N];
    for (reference, valeur) in r.iter_mut().zip(
        m.iter()
            .map(|l| l.iter().zip(v.iter()).map(|(a, b)| a * b).sum()),
    ) {
        *reference = valeur;
    }
    r
}

fn produit_parallele_matrice_vecteur(m: &[[u32; N]; N], v: &[u32; N]) -> [u32; N] {
    let mut r = [0; N];
    r.par_iter_mut()
        .zip(
            m.par_iter()
                .map(|l| l.par_iter().zip(v.par_iter()).map(|(a, b)| a * b).sum()),
        )
        .for_each(|(reference, valeur)| *reference = valeur);
    r
}

fn produit_matrice_matrice(m1: &[[u32; N]; N], m2: &[[u32; N]; N]) -> [[u32; N]; N] {
    let mut r = [[0; N]; N];
    r.par_iter_mut()
        .zip(m1.par_iter())
        .for_each(|(ligne_r, ligne_m1)| {
            ligne_r
                .par_iter_mut()
                .enumerate()
                .for_each(|(index_colonne, reference_r)| {
                    *reference_r = ligne_m1
                        .par_iter()
                        .zip(
                            (0..N)
                                .into_par_iter()
                                .map(|index_ligne| m2[index_ligne][index_colonne]),
                        )
                        .map(|(a, b)| a * b)
                        .sum()
                })
        });
    r
}

fn main() {
    let mut m = [[0; N]; N];
    for (index, ligne) in m.iter_mut().enumerate() {
        for reference in ligne.iter_mut() {
            *reference = index as u32;
        }
    }
    println!("m est {:?}", m);

    let mut v = [0; N];
    for (index, reference) in v.iter_mut().enumerate() {
        *reference = index as u32;
    }
    println!("v est {:?}", v);

    let p = produit_matrice_vecteur(&m, &v);
    println!("le produit est {:?}", p);

    let p2 = produit_parallele_matrice_vecteur(&m, &v);
    println!("le produit en // est {:?}", p2);

    let mut identite = [[0; N]; N];
    for (index, ligne) in identite.iter_mut().enumerate() {
        ligne[index] = 1;
    }
    println!("identite: {:?}", identite);
    let encore_m = produit_matrice_matrice(&m, &identite);
    println!("apres le produit, on a toujours {:?}", encore_m);
}
