use itertools::Itertools;
use rand::random;
use std::iter::repeat_with;

fn sac_a_dos() {
    let (volumes, gains): (Vec<u32>, Vec<u32>) = repeat_with(random::<u32>)
        .map(|e| 1 + (e % 100))
        .tuples()
        .take(10)
        .sorted_by_key(|(v, g)| v / g)
        .unzip();

    println!("volumes: {:?}, gains: {:?}", volumes, gains);

    let dernier_pris = volumes
        .iter()
        .scan(0, |s, &v| {
            *s += v;
            Some(*s)
        })
        .take_while(|&s| s <= 100) // le volume du sac est 100
        .count();

    let valeur = gains.iter().take(dernier_pris).sum::<u32>();
    let valeur_suivante = gains.get(dernier_pris).cloned();
    let valeur_finale = valeur_suivante
        .map(|v| std::cmp::max(v, valeur))
        .unwrap_or(valeur);
    println!("la solution vaut: {}", valeur_finale);
}

fn bin_packing() {
    let tailles: Vec<f64> = repeat_with(random).take(10).collect();
    eprintln!("tailles: {:?}", tailles);
    // on calcule les bins.
    // il s'agit d'un vecteur tel que chaque case represente une bin.
    // elle contient
    // - la place restante
    // - un vecteur contenant tout le contenu de la bin.
    let bins: Vec<(f64, Vec<f64>)> = tailles.iter().cloned().fold(Vec::new(), |mut bins, t| {
        let choix = bins
            .iter_mut()
            .filter(|(place_libre, _)| *place_libre >= t)
            .next(); // on prend la premiere bin avec assez de place
        // impossible d'afficher bins car le vecteur est borrow par choix
        if let Some((place_libre, contenu)) = choix {
            // modification directement sur bins (iter_mut)
            *place_libre -= t;
            contenu.push(t);
        } else {
            // si choix est None on rajoute une nouvelle bin.
            bins.push((1.0 - t, vec![t]));
        }
        bins
    });
    eprintln!("bins: {:?}", bins);
}

fn main() {
    println!("sac a dos :");
    sac_a_dos();

    println!("\n*********************************\n");

    println!("bin packing :");
    bin_packing();
}
