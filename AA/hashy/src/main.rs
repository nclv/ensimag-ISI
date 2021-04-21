use rand::prelude::*;
use rayon::prelude::*;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::iter::once;
use std::iter::repeat_with;
use std::sync::atomic::{AtomicBool, Ordering};

/// Renvoie le ieme hash de e.
fn hashes(e: u32, i: usize) -> usize {
    let seed = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]; // une racine constante pour etre toujours deterministe
    let mut rng = SmallRng::from_seed(seed);
    once(e as usize) // on commence par soi meme
        .chain(repeat_with(move || (rng.gen::<usize>() ^ e as usize)))
        .nth(i)
        .unwrap()
}

/// Renvoie le nombre de collisions obtenues en inserant chaque entree e
/// dans un tableau a la position hashes(e, i) modulo la taille du tableau.
/// (en utilisant la ieme fonction de hachage)
fn nombre_collisions_seq(taille: usize, entree: &[u32], i: usize) -> usize {
    let mut utilisation = vec![0; taille]; // on compte l'utilisation de chaque case
    for hash in entree.iter().map(|&e| hashes(e, i) % taille) {
        utilisation[hash] += 1;
    }
    utilisation.iter().filter(|&u| *u > 1).sum()
}

/// Renvoie si l'element de valeur e tombe en collision avec quelqu'un d'autre.
/// Calcul en W=O(n), D=O(log(n))
fn est_en_collision(taille: usize, entree: &[u32], e: u32, i: usize) -> bool {
    entree
        .par_iter()
        .filter(|&e2| hashes(*e2, i) % taille == hashes(e, i) % taille)
        .count()
        > 1
}

/// Renvoie le nombre de collisions obtenues en inserant chaque entree e
/// dans un tableau a la position hashes(e, i) modulo la taille du tableau.
/// (en utilisant la premiere fonction de hachage).
/// Calcul en parallele en W=O(n^2). Pas de variables atomiques.
fn nombre_collisions_par(taille: usize, entree: &[u32], i: usize) -> usize {
    entree
        .par_iter()
        .filter(|&e| est_en_collision(taille, entree, *e, i))
        .count()
}

/// Avec un tri parallele W=O(n log(n)).
fn nombre_collisions_par_tri(taille: usize, entree: &[u32], i: usize) -> usize {
    let n = entree.len();
    if n == 1 {
        return 1;
    }
    let mut indices_utilises: Vec<usize> =
        entree.par_iter().map(|&e| hashes(e, i) % taille).collect();
    indices_utilises.par_sort();
    let mut nb_uniques = indices_utilises
        .par_windows(3)
        .filter(|&s| s[0] != s[1] && s[1] != s[2])
        .count();
    nb_uniques += (indices_utilises[0] != indices_utilises[1]) as usize
        + (indices_utilises[n - 1] != indices_utilises[n - 2]) as usize;
    n - nb_uniques
}

struct TablePartagee<'a>(UnsafeCell<&'a mut [u32]>);
unsafe impl<'a> Sync for TablePartagee<'a> {}

/// On s'autorise maintenant l'utilisation de booleens atomiques.
/// On s'autorisera egalement des acces en ecriture en parallele sur la table
/// a condition qu'ils touchent tous des cases differentes.
/// On cherche a placer les elements de l'entree dans la table selon l'algo suivant:
/// chaque element cherche a se placer sur l'indice donne par le hash.
/// En cas de collision un seul reussit.
/// Tous ceux qui echouent a se placer sont renvoyes dans un vecteur.
fn place(table: &mut [u32], entree: &[u32], i: usize) -> Vec<u32> {
    let taille = table.len();
    let utilise: Vec<AtomicBool> =
        repeat_with(Default::default).take(taille).collect();
    let cell = TablePartagee(UnsafeCell::new(table));
    entree
        .par_iter()
        .cloned()
        .filter(|&e| {
            let indice = hashes(e, i) % taille;
            let deja_pris =
                utilise[indice].compare_and_swap(false, true, Ordering::SeqCst);
            if deja_pris {
                true // on garde e pour le vecteur de retours
            } else {
                let table = unsafe { cell.0.get().as_mut() }.unwrap();
                table[indice] = e;
                false
            }
        })
        .collect()
}

/// Renvoie le (ou un des) element le moins frequent du tableau donne.
fn element_moins_frequent(elements: &[u32]) -> u32 {
    let compte: HashMap<u32, usize> = elements
        .par_iter()
        .fold(HashMap::new, |mut h, &e| {
            *h.entry(e).or_insert(0) += 1;
            h
        })
        .reduce(HashMap::new, |h1, h2| {
            h1.par_iter()
                .filter_map(|(e, c1)| {
                    if let Some(c2) = h2.get(e) {
                        Some((*e, *c1 + *c2))
                    } else {
                        Some((*e, *c1))
                    }
                })
                .chain(h2.par_iter().filter_map(|(e, c2)| {
                    if h1.get(e).is_none() {
                        Some((*e, *c2))
                    } else {
                        None
                    }
                }))
                .collect()
        });
    compte
        .par_iter()
        .min_by_key(|&(_, c)| c)
        .map(|(e, _)| *e)
        .unwrap()
}

fn main() {
    assert_eq!(nombre_collisions_seq(4, &[0, 3, 7], 0), 2);
    assert_eq!(nombre_collisions_seq(4, &[0, 3, 7, 4, 11, 2], 0), 5);
    assert_eq!(nombre_collisions_par(4, &[0, 3, 7], 0), 2);
    assert_eq!(nombre_collisions_par(4, &[0, 3, 7, 4, 11, 2], 0), 5);
    assert_eq!(nombre_collisions_par_tri(4, &[0, 3, 7], 0), 2);
    assert_eq!(nombre_collisions_par_tri(4, &[0, 3, 7, 4, 11, 2], 0), 5);
    let mut destination = vec![0; 10];
    let reste = place(&mut destination, &[1, 2, 4, 7, 14, 17, 27], 0);
    assert_eq!(reste.len(), 3);
    assert_eq!(destination[1], 1);
    assert_eq!(destination[2], 2);
    assert_eq!(destination[4] % 10, 4);
    assert_eq!(destination[7] % 10, 7);
    assert_eq!(reste.iter().filter(|&e| *e % 10 == 7).count(), 2);
    assert_eq!(
        element_moins_frequent(&[1, 2, 3, 2, 3, 1, 2, 2, 3, 3, 1]),
        1
    );
}
