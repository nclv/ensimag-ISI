#![warn(clippy::all)]
use rayon::prelude::*;

// additionne a et b avec la retenue donnee et renvoie le vecteur resultat avec une retenue
fn addition(a: &[u32], b: &[u32], retenue: u32) -> (Vec<u32>, u32) {
    assert_eq!(a.len(), b.len());
    if a.is_empty() {
        (Vec::new(), 0)
    } else if a.len() == 1 {
        let s = a[0] + b[0] + retenue;
        (vec![s % 10], s / 10)
    } else {
        let milieu = a.len() / 2;
        let (a1, a2) = a.split_at(milieu);
        let (b1, b2) = b.split_at(milieu);
        let ((v1, r1), ((v1_r, r1_r), (v2, r2))) = rayon::join(
            || addition(a1, b1, 0),
            || rayon::join(|| addition(a1, b1, 1), || addition(a2, b2, retenue)),
        );
        if r2 == 0 {
            (v1.par_iter().chain(v2.par_iter()).cloned().collect(), r1)
        } else {
            (
                v1_r.par_iter().chain(v2.par_iter()).cloned().collect(),
                r1_r,
            )
        }
    }
}

// ajoute 1 au nombre stocke dans s, renvoie vrai si tous les chiffres etaient 9
fn increment(s: &mut [u32]) -> bool {
    if let Some((limite, _)) = s.par_iter().enumerate().find_last(|&(indice, chiffre)| {
        *chiffre != 9 && (indice == (s.len() - 1) || s[indice + 1] == 9)
    }) {
        s[limite] += 1;
        s[(limite + 1)..].par_iter_mut().for_each(|v| *v = 0);
        false
    } else {
        s.par_iter_mut().for_each(|v| *v = 0);
        true
    }
}

// additionne a et b dans la tranche donnee
// renvoie s'il y a une retenue
fn addition2(a: &[u32], b: &[u32], r: &mut [u32]) -> bool {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), r.len());
    if a.is_empty() {
        false
    } else if a.len() == 1 {
        let s = a[0] + b[0];
        r[0] = s % 10;
        s >= 10
    } else {
        let milieu = a.len() / 2;
        let (a1, a2) = a.split_at(milieu);
        let (b1, b2) = b.split_at(milieu);
        let (r1, r2) = r.split_at_mut(milieu);
        let (retenue1, retenue2) = rayon::join(|| addition2(a1, b1, r1), || addition2(a2, b2, r2));
        if retenue2 {
            increment(r1) || retenue1
        } else {
            retenue1
        }
    }
}

fn main() {
    let a = [1, 2, 3, 4];
    let b = [5, 6, 7, 8];
    println!("a: {:?}, b: {:?}", a, b);
    let (resultat, _) = addition(&a, &b, 0);
    println!("somme : {:?}", resultat);

    let x = [0, 1, 5, 9, 9, 9, 9, 9];
    let mut y = x;
    increment(&mut y);
    println!("test increment {:?} -> {:?}", x, y);

    let x = [0, 1, 5, 3, 2, 3, 2, 7];
    let mut y = x;
    increment(&mut y);
    println!("test increment {:?} -> {:?}", x, y);

    let x = [0, 1, 5, 3, 2, 3, 2, 9];
    let mut y = x;
    increment(&mut y);
    println!("test increment {:?} -> {:?}", x, y);

    let x = [9, 9, 9];
    let mut y = x;
    increment(&mut y);
    println!("test increment {:?} -> {:?}", x, y);

    let a = [1, 2, 3, 4];
    let b = [5, 6, 7, 8];
    let mut resultat = [0; 4];
    println!("a: {:?}, b: {:?}", a, b);
    addition2(&a, &b, &mut resultat);
    println!("somme : {:?}", resultat);
}
