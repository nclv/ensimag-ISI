#![warn(clippy::all)]
use std::borrow::BorrowMut;
use std::iter::repeat_with;
use std::mem::swap;

fn tri_selection(tranche: &mut [u32]) {
    for indice_cible in 0..(tranche.len() - 1) {
        let indice_min = tranche
            .iter()
            .enumerate()
            .skip(indice_cible)
            .min_by_key(|&(_, v)| v)
            .map(|(i, _)| i)
            .unwrap();
        tranche.swap(indice_cible, indice_min);
    }
}

// seconde version, pour changer, attention ca pique tres fort
fn tri_selection2(tranche: &mut [u32]) {
    let mut restant = tranche;
    while let Some((premier, fin)) = { restant }.split_first_mut() {
        {
            if let Some(ref_min) = fin.iter_mut().min() {
                if ref_min.lt(&premier) {
                    swap(ref_min, premier);
                }
            }
        }
        restant = fin;
    }
}

fn tri_selection_generique<B: BorrowMut<[T]>, T: Ord>(donnees: &mut B) {
    let tranche = donnees.borrow_mut();
    for indice_cible in 0..(tranche.len() - 1) {
        let indice_min = tranche
            .iter()
            .enumerate()
            .skip(indice_cible)
            .min_by_key(|&(_, v)| v)
            .map(|(i, _)| i)
            .unwrap();
        tranche.swap(indice_cible, indice_min);
    }
}

const TAILLE: usize = 10;

fn main() {
    // on cree un vecteur aleatoire avec un for
    let mut v = Vec::with_capacity(TAILLE);
    for _ in 0..TAILLE {
        v.push(rand::random::<u32>() % (TAILLE as u32));
    }
    println!("entree: {:?}", v);
    // on trie
    tri_selection(v.as_mut_slice());
    println!("sortie: {:?}", v);

    // on cree un vecteur aleatoire avec un map + collect
    let mut r: Vec<_> = (0..TAILLE)
        .map(|_| rand::random::<u32>() % (TAILLE as u32))
        .collect();
    println!("entree: {:?}", r);
    tri_selection2(r.as_mut_slice());
    println!("sortie: {:?}", r);

    // on cree un vecteur aleatoire avec un repeat_with + collect
    let mut w: Vec<_> = repeat_with(|| rand::random::<u32>() % (TAILLE as u32))
        .take(TAILLE)
        .collect();
    println!("entree: {:?}", w);
    // on trie
    tri_selection_generique(&mut w);
    println!("sortie: {:?}", w);
}
