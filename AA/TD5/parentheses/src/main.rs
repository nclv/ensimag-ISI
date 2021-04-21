#![warn(clippy::all)]
use rayon::prelude::*;
use std::collections::LinkedList;

fn calcul_pi(chaine: &str) -> Vec<i32> {
    // NB: il s'agit en realite d'un prefixe
    chaine
        .par_chars()
        .map(|c| if c == '(' { 1 } else { -1 })
        .fold(Vec::new, |mut v, x| {
            let nouvelle_valeur = v.last().cloned().unwrap_or(0) + x;
            v.push(nouvelle_valeur);
            v
        })
        .map(|v| {
            let mut l = LinkedList::new();
            l.push_back(v);
            l
        })
        .reduce(LinkedList::new, |mut l1, mut l2| {
            l1.append(&mut l2);
            l1
        })
        .into_iter()
        .fold(Vec::new(), |mut v1, v2| {
            let dernier = v1.last().cloned().unwrap_or(0);
            v1.par_extend(v2.par_iter().map(|x| *x + dernier));
            v1
        })
}

fn correctement_parenthesee(chaine: &str) -> bool {
    let pi = calcul_pi(chaine);
    *pi.last().unwrap() == 0 && pi.par_iter().all(|p| *p >= 0)
}

/// Renvoie l'indice de la parenthese ouvrante correspondante.
/// Pre-suppose la chaine bien parenthesee.
fn mise_en_correspondance(chaine: &str, indice_fermante: usize, pi: &[i32]) -> usize {
    chaine
        .as_bytes() // on passe sur un tableau d'octets
        .par_iter() // on recupere un iterateur // sur les char (octets)
        .zip(pi.par_iter()) // on zippe avec pi
        .take(indice_fermante) // on s'arrete avant la fermante
        .enumerate() // on numerote car on cherche un indice
        .find_last(|&(_, (c, p))| *c == b'(' && *p == pi[indice_fermante] + 1) // on cherche le dernier match
        .map(|(i, _)| i) // on jette les infos inutiles
        .unwrap()
}

/// Renvoie l'indice de chaque parenthese ouvrante et pour
/// chaque fermante l'indice de la parenthese ouvrante correspondante.
fn apparier(chaine: &str) -> Vec<usize> {
    let pi = calcul_pi(chaine);
    chaine
        .as_bytes()
        .par_iter()
        .enumerate()
        .map(|(i, c)| {
            if *c == b'(' {
                i
            } else {
                mise_en_correspondance(chaine, i, &pi)
            }
        })
        .collect()
}

/// Renvoie le nombre de parentheses ouvrantes non fermees
/// et le nombre de parentheses fermantes non ouvertes.
/// version sequentielle.
fn reduire_sequentiel(caracteres: &[u8]) -> (u32, u32) {
    let mut compte: i32 = 0;
    let mut fermantes_non_ouvertes = 0;
    for c in caracteres {
        if *c == b'(' {
            compte += 1;
        } else if compte == 0 {
            fermantes_non_ouvertes += 1;
        } else {
            compte -= 1;
        }
    }
    (
        if compte > 0 { compte as u32 } else { 0 },
        fermantes_non_ouvertes,
    )
}

/// Renvoie le nombre de parentheses ouvrantes non fermees
/// et le nombre de parentheses fermantes non ouvertes.
/// version parallele.
fn reduire(caracteres: &[u8], limite: usize) -> (u32, u32) {
    if caracteres.len() <= limite {
        reduire_sequentiel(caracteres)
    } else {
        let milieu = caracteres.len() / 2;
        let (c1, c2) = caracteres.split_at(milieu);
        let ((o1, f1), (o2, f2)) = rayon::join(|| reduire(c1, limite), || reduire(c2, limite));
        if o1 > f2 {
            (o2 + o1 - f2, f1)
        } else {
            (o2, f1 + f2 - o1)
        }
    }
}

fn main() {
    let s = "(())((())())";
    println!("la chaine est {}", s);
    let pi = calcul_pi(s);
    println!("pi est {:?}", pi);
    println!("parenthesage ok ? {}", correctement_parenthesee(s));
    for (i, c) in s.chars().enumerate() {
        if c == ')' {
            println!(
                "l'ouvrante de {} est {}",
                i,
                mise_en_correspondance(s, i, &pi)
            );
        }
    }
    println!("apparier: {:?}", apparier(s));
    println!("reduire: {:?}", reduire(s.as_bytes(), 1));
    let s2 = ")(())(";
    println!("reduire sur {}: {:?}", s2, reduire(s2.as_bytes(), 1));
}
