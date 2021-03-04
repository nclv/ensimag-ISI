#![warn(clippy::all)]
use rayon::prelude::*;
use time::now;

fn f(i: u32) -> u32 {
    if (i == 0) || (i == 1) {
        i
    } else {
        f(i - 1) + f(i - 2)
    }
}

fn creation_vecteur_seq(n: u32) -> Vec<u32> {
    (0..n).map(f).collect()
}

fn creation_vecteur_par(n: u32) -> Vec<u32> {
    (0..n).into_par_iter().map(f).collect()
}

fn somme_vecteur(v: &[u32]) -> u32 {
    v.par_iter().sum()
}

const N: usize = 10;

fn sommes_lignes_egales(matrice: &[[i32; N]; N]) -> bool {
    let somme = matrice[0].par_iter().sum();
    matrice[1..]
        .par_iter()
        .all(|l| l.par_iter().sum::<i32>() == somme)
}

fn main() {
    let start = now();
    let vseq = creation_vecteur_seq(40);
    println!("creation sequentielle en {}", now() - start);
    let start = now();
    let vpar = creation_vecteur_par(40);
    println!("creation parallele en {}", now() - start);
    assert_eq!(vseq, vpar);
    println!("la somme vaut: {}", somme_vecteur(&vseq));

    let mut matrice = [[1; N]; N];
    matrice[0][0] += 1;
    matrice[0][1] -= 1;
    matrice[1][1] += 2;
    matrice[1][2] -= 2;
    assert!(sommes_lignes_egales(&matrice))
}
