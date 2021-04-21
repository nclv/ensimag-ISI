use rayon::prelude::*;
use rayon_logs::{join_context, Logged, ThreadPoolBuilder};

fn produit(entree: &[u64]) -> u64 {
    reduce(entree, || 1, |a, b| a * b)
}

fn somme(entree: &[u64]) -> u64 {
    reduce(entree, || 0, |a, b| a + b)
}

fn reduce<T, ID, OP>(entree: &[T], identity: ID, op: OP) -> T
where
    T: Copy + Send + Sync,
    ID: Fn() -> T + Sync,
    OP: Fn(T, T) -> T + Sync,
{
    reduce_rec(entree, &identity, &op, 2 * rayon::current_num_threads())
}

fn reduce_rec<T, ID, OP>(entree: &[T], identity: &ID, op: &OP, compte: usize) -> T
where
    T: Copy + Send + Sync,
    ID: Fn() -> T + Sync,
    OP: Fn(T, T) -> T + Sync,
{
    if compte <= 0 || entree.len() <= 1 {
        entree.iter().copied().fold(identity(), op)
    } else {
        let mid = entree.len() / 2;
        let (gauche, droite) = entree.split_at(mid);
        let (s_gauche, s_droite) = join_context(
            |_| reduce_rec(gauche, identity, op, compte / 2),
            |c| {
                reduce_rec(
                    droite,
                    identity,
                    op,
                    if c.migrated() {
                        2 * rayon::current_num_threads()
                    } else {
                        compte / 2
                    },
                )
            },
        );
        op(s_gauche, s_droite)
    }
}

fn main() {
    let e = (0..1_000_000).map(|e| e % 2).collect::<Vec<u64>>();
    let pool = ThreadPoolBuilder::new()
        .build()
        .expect("echec de la creation du pool");
    let (_, log) = pool.logging_install(|| assert_eq!(500_000, somme(&e)));
    log.save_svg("reduction.svg")
        .expect("echec de la sauvegarde");

    let (_, log) =
        pool.logging_install(|| assert_eq!(500_000, Logged::new(e.par_iter()).sum::<u64>()));
    log.save_svg("rayon.svg").expect("echec de la sauvegarde");
}
