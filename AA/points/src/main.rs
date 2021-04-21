use rand::prelude::*;
use rayon::prelude::*;

type Point = (u32, u32);

// fn creation_points_fausse(taille: usize) -> Vec<Point> {
//     let mut v = Vec::new();
//     (0..taille).into_par_iter().for_each(|_| v.push(random()));
//     v
// }

fn creation_points(taille: usize) -> Vec<Point> {
    (0..taille).into_par_iter().map(|_| random()).collect()
}

/// Renvoie la distance entre deux points (manhattan).
/// On ment en cas d'overflow mais ce n'est pas grave car on cherche la
/// distance min.
fn distance(p1: &Point, p2: &Point) -> u32 {
    let gros_x = p1.0.max(p2.0);
    let petit_x = p1.0.min(p2.0);
    let gros_y = p1.1.max(p2.1);
    let petit_y = p1.1.min(p2.1);
    (gros_x - petit_x).saturating_add(gros_y - petit_y)
}

fn collect_manuel<I: IndexedParallelIterator>(iterateur: I) -> Vec<I::Item> {
    let mut v = Vec::with_capacity(iterateur.len());
    unsafe { v.set_len(iterateur.len()) }
    //NB: le write evite le drop de la valeur de s avant remplissage par e
    iterateur
        .zip(&mut v)
        .for_each(|(e, s)| unsafe { (s as *mut I::Item).write(e) });
    v
}

/// renvoie la distance minimale de `p` a un point de `points`
/// si la tranche de points n'est pas vide et None sinon.
fn distance_min_p(points: &[Point], p: &Point) -> Option<u32> {
    points.par_iter().map(|p2| distance(p, p2)).min()
}

/// renvoie la distance min entre deux points de `points` ou None
/// si `points` est de longueur <= 1
fn distance_min(points: &[Point]) -> Option<u32> {
    (0..points.len())
        .into_par_iter()
        .filter_map(|i| {
            let tranche = &points[i..];
            tranche
                .split_first()
                .and_then(|(premier, reste)| distance_min_p(reste, premier))
        })
        .min()
}

// deuxieme ecriture, a l'aide de `flat_map`.
// je n'en ai pas trop parle en cours.
// on fera des monades dans une vie prochaine.
fn distance_min_2(points: &[Point]) -> Option<u32> {
    (0..points.len()) // la range des indices de point
        .into_par_iter() // iterateur sur les indices de points
        // on va maintenant transformer chaque indice i
        // en iterateur parallele sur tous les indices j a partir de i+1
        // puis en iterateur parallele sur tous les couples (i,j) d'indices
        .flat_map(|i| ((i + 1)..points.len()).into_par_iter().map(move |j| (i, j)))
        .map(|(i, j)| distance(&points[i], &points[j]))
        .min()
}

/// renvoie la distance min sur un échantillon de `r` couples
/// aléatoires de points. On supposera r > 0 et le nombre de points > 2.
fn echantillonage(points: &[Point], r: usize) -> u32 {
    (0..r)
        .into_par_iter()
        .map(|_| {
            let i = random::<usize>() % points.len();
            let mut j = random::<usize>() % (points.len() - 1);
            if j >= i {
                j += 1
            }
            distance(&points[i], &points[j])
        })
        .min()
        .unwrap()
}

// juste pour le fun, je vous met le vecteur concurrent.
// c'est la fete du unsafe.
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicUsize, Ordering};

struct VecConcurrent<T> {
    indice: AtomicUsize,
    // la seule maniere de partager quelque chose
    // de non atomique en ecriture en rust (tout en faisant des acces concurrents).
    // pas de pb ici car chaque thread ecrit sur une case differente
    tableau: UnsafeCell<Box<[T]>>,
}

impl<T> VecConcurrent<T> {
    fn new(taille: usize) -> Self {
        let mut v = Vec::with_capacity(taille);
        unsafe { v.set_len(taille) }
        VecConcurrent {
            indice: AtomicUsize::new(0),
            tableau: UnsafeCell::new(v.into_boxed_slice()),
        }
    }
    fn push(&self, elem: T) {
        let i = self.indice.fetch_add(1, Ordering::SeqCst);
        let tableau = unsafe { self.tableau.get().as_mut().unwrap() };
        assert!(i < tableau.len());
        unsafe { (&mut tableau[i] as *mut T).write(elem) }
    }
    fn into_vec(self) -> Vec<T> {
        let mut v = self.tableau.into_inner().into_vec();
        unsafe { v.set_len(self.indice.into_inner()) }
        v
    }
}

unsafe impl<T: Sync> Sync for VecConcurrent<T> {}

// dans toute la suite, il y a "trop" de parallelisme pour
// une utilisation reelle. c'est pour pousser le vice jusqu'au bout.
// je pourrais prendre des refs vers les points mais je vais vous
// epargner les lifetimes en les copiant.

// chaque carre est un vecteur de Point.
// on a plein de carres dans un espace en 2d.
// il nous faut donc un vecteur de vecteur de vecteur de points.
// de rien, je savais que ca vous plairait.
type Carres = Vec<Vec<Vec<Point>>>;

fn creation_carres(points: &[Point], longueur_cote: u32) -> Carres {
    let nombre_carres_1d = u32::MAX / longueur_cote + 1; // +1 pour l'arrondi
    let nombre_carres = nombre_carres_1d * nombre_carres_1d;
    let taille = 3 + points.len() / nombre_carres as usize * 2;
    // on commence par creer tous les carres
    let carres_concurrents = (0..nombre_carres_1d)
        .into_par_iter()
        .map(|_| {
            (0..nombre_carres_1d)
                .into_par_iter()
                .map(|_| VecConcurrent::new(taille))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    // on remplit
    points.par_iter().for_each(|p| {
        let (x, y) = p;
        let indice_1 = (x / longueur_cote) as usize;
        let indice_2 = (y / longueur_cote) as usize;
        carres_concurrents[indice_1][indice_2].push(*p)
    });
    // je reconvertis en vecteurs normaux
    carres_concurrents
        .into_par_iter()
        .map(|l| l.into_par_iter().map(|c| c.into_vec()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

// le produit cartesien de A et B
fn produit<A, B>(a: A, b: B) -> impl ParallelIterator<Item = (A::Item, B::Item)>
where
    A: IndexedParallelIterator + Clone + Sync,
    B: ParallelIterator + Clone + Sync,
    A::Item: Sync + Copy,
    B::Item: Sync,
{
    let taille = a.len();
    a.zip(rayon::iter::repeatn(b, taille))
        .flat_map(|(ea, b_clone)| b_clone.map(move |eb| (ea, eb)))
}

/// renvoie un iterateur parallele sur tous les carres qui sont
/// voisins du carre en position (i,j)
fn carres_voisins<'a>(
    carres: &'a [Vec<Vec<Point>>],
    i: usize,
    j: usize,
) -> impl ParallelIterator<Item = &'a [Point]> + 'a {
    let i_min = i.saturating_sub(1);
    let i_max = (i + 2).min(carres.len());
    let j_min = j.saturating_sub(1);
    let j_max = (j + 2).min(carres.len());
    produit(
        (i_min..i_max).into_par_iter(),
        (j_min..j_max).into_par_iter(),
    )
    .filter(move |&(i_voisin, j_voisin)| i != i_voisin || j != j_voisin)
    .map(move |(i, j)| carres[i][j].as_slice())
}

fn distance_min_entre_carres(c1: &[Point], c2: &[Point]) -> Option<u32> {
    c1.par_iter()
        .filter_map(|p1| c2.par_iter().map(|p2| distance(p1, p2)).min())
        .min()
}

/// l'algo complet avec l'echantillonage et les carres
fn distance_min_avec_carres(points: &[Point], r: usize) -> Option<u32> {
    let d_r = echantillonage(points, r);
    // je vais eviter de creer trop de carres,
    // en montant artificiellement la distance.
    // on pourrait s'en sortir mieux en
    // prenant une table de HashMap<(usize, usize), Vec<Point>>
    // plutot qu'un Vec<Vec<Vec<Point>>>.
    // mais bon, ca va faire trop.
    let d_r = std::cmp::max(d_r, 1_000_000);
    let carres = creation_carres(points, d_r);
    let dimension = carres.len();
    let (m1, m2) = rayon::join(
        || {
            // entre carres voisins
            produit(
                (0..dimension).into_par_iter(),
                (0..dimension).into_par_iter(),
            )
            .filter_map(|(i, j)| {
                let c1 = carres[i][j].as_slice();
                // on recupere le min pour chaque carre avec ses voisins
                carres_voisins(&carres, i, j)
                    .filter_map(|c2| distance_min_entre_carres(c1, c2))
                    .min()
            })
            .min()
        },
        || {
            // en interne a chaque carre
            carres
                .par_iter()
                .flat_map(|l| l.par_iter())
                .filter_map(|c| distance_min(c))
                .min()
        },
    );
    std::cmp::min(m1, m2)
}

fn main() {
    // un petit test, juste pour verifier la correction
    let points = creation_points(40_000);
    let m1 = distance_min(&points);
    println!("m1: {:?}", m1);
    let m2 = distance_min_2(&points);
    println!("m2: {:?}", m2);
    let m3 = distance_min_avec_carres(&points, 20);
    println!("m3: {:?}", m3);
    assert_eq!(m1, m2);
    assert_eq!(m2, m3);
}
