use rayon_logs::{join, ThreadPoolBuilder};

fn somme(entree: &[u64]) -> u64 {
    if entree.len() <= 5_000 {
        entree.iter().sum()
    } else {
        let mid = entree.len() / 2;
        let (gauche, droite) = entree.split_at(mid);
        let (s_gauche, s_droite) = join(|| somme(gauche), || somme(droite));
        s_gauche + s_droite
    }
}

fn main() {
    let e = (0..1_000_000).collect::<Vec<u64>>();
    let pool = ThreadPoolBuilder::new()
        .build()
        .expect("echec de la creation du pool");
    let (_, log) = pool.logging_install(|| assert_eq!(500_000 * 999_999, somme(&e)));
    log.save_svg("somme.svg").expect("echec de la sauvegarde");
}
