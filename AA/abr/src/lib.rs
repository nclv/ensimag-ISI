//! creation d'abr en parallele
//!
//! idees pour extensions:
//! - faire un collect parallele
//! - faire la decoupe en petits/grands en une seule passe
//! - faire un extend parallele
//! - en parallele : collecter de l'arbre dans un vecteur tous les elements entre un min et un max
#![feature(test)]
extern crate rand;
extern crate rayon;
extern crate test;

use rayon::prelude::*;
use std::collections::LinkedList;

#[derive(Debug, PartialEq, Eq)]
pub struct Noeud {
    clef: u32,
    fils: [Option<Box<Noeud>>; 2],
}

impl Noeud {
    pub fn new(clef: u32) -> Self {
        Noeud {
            clef,
            fils: [None, None],
        }
    }

    pub fn inserer(&mut self, nouvelle_clef: u32) {
        let direction = (self.clef < nouvelle_clef) as usize;
        if let Some(ref mut fils) = self.fils[direction] {
            fils.inserer(nouvelle_clef)
        } else {
            self.fils[direction] = Some(Box::new(Noeud::new(nouvelle_clef)))
        }
    }
}

pub fn somme_sequentielle_pairs(racine: &Option<Box<Noeud>>) -> u32 {
    racine.as_ref().map_or(0, |noeud| {
        noeud
            .fils
            .iter()
            .map(|f| somme_sequentielle_pairs(f))
            .sum::<u32>() + if noeud.clef % 2 == 0 { noeud.clef } else { 0 }
    })
}

/// Somme parallele des clefs paires.
/// NB: avec un join au lieu d'un join_context c'est le speeddown assure
pub fn somme_parallele_pairs(racine: &Option<Box<Noeud>>) -> u32 {
    racine.as_ref().map_or(0, |noeud| {
        //noeud.fils.par_iter().map(|f| somme_parallele_pairs(f)).sum::<u32>() + if noeud.clef % 2 == 0 { noeud.clef } else { 0 }
        let (s1, s2) = rayon::join_context(
            |_| somme_parallele_pairs(&noeud.fils[0]),
            |c| {
                if c.migrated() {
                    somme_parallele_pairs(&noeud.fils[1])
                } else {
                    somme_sequentielle_pairs(&noeud.fils[1])
                }
            },
        );
        s1 + s2 + if noeud.clef % 2 == 0 { noeud.clef } else { 0 }
    })
}

pub fn creation_tres_parallele(tranche: &[u32]) -> Option<Box<Noeud>> {
    if let Some((pivot, reste)) = tranche.split_first() {
        let petits: Vec<u32> = reste.par_iter().filter(|i| *i < pivot).cloned().collect();
        let grands: Vec<u32> = reste.par_iter().filter(|i| *i > pivot).cloned().collect();
        let (arbre_petits, arbre_grands) = rayon::join(
            || creation_tres_parallele(&petits),
            || creation_tres_parallele(&grands),
        );
        Some(Box::new(Noeud {
            clef: *pivot,
            fils: [arbre_petits, arbre_grands],
        }))
    } else {
        None
    }
}

pub fn creation_sequentielle(tranche: &[u32]) -> Option<Box<Noeud>> {
    if let Some((premier, suite)) = tranche.split_first() {
        let mut racine = Box::new(Noeud {
            clef: *premier,
            fils: [None, None],
        });
        for e in suite {
            racine.inserer(*e);
        }
        Some(racine)
    } else {
        None
    }
}

pub fn creation_tres_rapide(tranche: &[u32], limite: usize) -> Option<Box<Noeud>> {
    if tranche.len() < limite {
        creation_sequentielle(tranche)
    } else {
        if let Some((&pivot, reste)) = tranche.split_first() {
            let (petits, grands) = reste.iter().fold(
                (
                    Vec::with_capacity(tranche.len()), // ca apporte bcp de perfs
                    Vec::with_capacity(tranche.len()), // de pre-allouer
                ),
                |(mut petits, mut grands), &x| {
                    if x < pivot {
                        petits.push(x)
                    } else {
                        grands.push(x)
                    };
                    (petits, grands)
                },
            );
            let (arbre_petits, arbre_grands) = rayon::join(
                || creation_tres_rapide(&petits, limite),
                || creation_tres_rapide(&grands, limite),
            );
            Some(Box::new(Noeud {
                clef: pivot,
                fils: [arbre_petits, arbre_grands],
            }))
        } else {
            None
        }
    }
}

/// Renvoie deux vecteurs: les elements plus petits que la limite
/// et ceux plus grands
pub fn decoupe<I: ParallelIterator<Item = u32>>(limite: u32, elements: I) -> (Vec<u32>, Vec<u32>) {
    let liste: LinkedList<(Vec<u32>, Vec<u32>)> = elements
        .fold(
            || (Vec::new(), Vec::new()),
            |mut acc, x| {
                if x < limite {
                    acc.0.push(x)
                } else {
                    acc.1.push(x)
                };
                acc
            },
        )
        .map(|v| {
            let mut l = LinkedList::new();
            l.push_back(v);
            l
        })
        .reduce(LinkedList::new, |mut l1, mut l2| {
            l1.append(&mut l2);
            l1
        });
    liste
        .into_iter()
        .fold((Vec::new(), Vec::new()), |mut acc, v| {
            acc.0.par_extend(v.0);
            acc.1.par_extend(v.1);
            acc
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};
    use std::iter::once;
    use test::Bencher;

    /// Retourne le tableau d'elements permettant de creer un arbre parfait (de taille donnee).
    /// pre-condition: taille est une puissance de 2 diminuee de 1.
    pub fn arbre_parfait(taille: u32) -> Vec<u32> {
        if taille == 0 {
            Vec::new()
        } else {
            let r = taille / 2;
            let a = arbre_parfait(r);
            once(r)
                .chain(a.iter().cloned())
                .chain(a.iter().map(|i| *i + r + 1))
                .collect()
        }
    }

    #[test]
    fn test_decoupe() {
        let mut elements: Vec<_> = (0..10_000).collect();
        let mut rng = rand::thread_rng();
        rng.shuffle(&mut elements);
        let (premier, reste) = elements.split_first().unwrap();
        let (petits, grands) = decoupe(*premier, reste.par_iter().cloned());
        assert!(petits.iter().all(|e| *e < *premier));
        assert!(grands.iter().all(|e| *e > *premier));
    }

    #[test]
    fn creations_identiques() {
        let mut elements: Vec<_> = (0..10_000).collect();
        let mut rng = rand::thread_rng();
        rng.shuffle(&mut elements);
        let arbre_sequentiel = creation_sequentielle(&elements);
        let arbre_parallele = creation_tres_parallele(&elements);
        let arbre_parallele2 = creation_tres_rapide(
            &elements,
            10 * ((elements.len() as f64).log(2.0).ceil() as usize),
        );
        assert_eq!(arbre_sequentiel, arbre_parallele);
        assert_eq!(arbre_sequentiel, arbre_parallele2);
    }

    #[test]
    fn sommes_pairs() {
        let mut elements: Vec<_> = (0..10_000).collect();
        let mut rng = rand::thread_rng();
        rng.shuffle(&mut elements);
        let arbre = creation_sequentielle(&elements);
        let s1 = somme_sequentielle_pairs(&arbre);
        let s2 = somme_parallele_pairs(&arbre);
        assert_eq!(s1, s2);
        assert_eq!(s1, (elements.len() / 2 * (elements.len() / 2 - 1)) as u32);
    }

    #[bench]
    fn somme_seq(b: &mut Bencher) {
        let elements = arbre_parfait(2_u32.pow(15) - 1);
        let arbre = creation_sequentielle(&elements);
        b.iter(|| {
            let s = somme_sequentielle_pairs(&arbre);
            assert_eq!(s, (elements.len() / 2 * (elements.len() / 2 + 1)) as u32);
        })
    }

    #[bench]
    fn somme_par(b: &mut Bencher) {
        let elements = arbre_parfait(2_u32.pow(15) - 1);
        let arbre = creation_sequentielle(&elements);
        b.iter(|| {
            let s = somme_parallele_pairs(&arbre);
            assert_eq!(s, (elements.len() / 2 * (elements.len() / 2 + 1)) as u32);
        })
    }

    #[bench]
    fn creation_seq(b: &mut Bencher) {
        b.iter(|| {
            let mut elements: Vec<_> = (0..100_000).collect();
            let mut rng = rand::thread_rng();
            rng.shuffle(&mut elements);
            let arbre = creation_sequentielle(&elements);
            assert_eq!(arbre.as_ref().unwrap().clef, elements[0]);
        })
    }
    #[bench]
    fn creation_par(b: &mut Bencher) {
        b.iter(|| {
            let mut elements: Vec<_> = (0..100_000).collect();
            let mut rng = rand::thread_rng();
            rng.shuffle(&mut elements);
            let arbre = creation_tres_parallele(&elements);
            assert_eq!(arbre.as_ref().unwrap().clef, elements[0]);
        })
    }
    #[bench]
    fn creation_rapide(b: &mut Bencher) {
        b.iter(|| {
            let mut elements: Vec<_> = (0..40_000).collect();
            let mut rng = rand::thread_rng();
            rng.shuffle(&mut elements);
            let arbre = creation_tres_rapide(
                &elements,
                10 * ((elements.len() as f64).log(2.0).ceil() as usize),
            );
            assert_eq!(arbre.as_ref().unwrap().clef, elements[0]);
        })
    }

}
