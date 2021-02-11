// use itertools::Itertools;

fn main() {
    println!("<svg width='800' height='600'>");
    let couleurs = ["red", "green", "blue", "purple", "yellow"];
    let taches = std::iter::repeat_with(|| 50 + rand::random::<u32>() % 100).take(20);
    // println!("{}", taches.clone().format(", "));
    // let taches = [100, 100, 100, 100, 100, 100, 100, 100, 100, 300];
    taches
        //  .iter()
        .zip(couleurs.iter().cycle())
        .fold([0; 4], |mut etat, (duree, couleur)| {
            let (proc, charge) = etat
                .iter_mut()
                .enumerate()
                .min_by_key(|(_, r)| **r)
                .unwrap();
            println!(
                "<rect x='{}' y='{}' width='{}' height='150' fill='{}'/>",
                *charge,
                proc * 150,
                duree,
                couleur
            );
            *charge += duree;
            etat
        });
    println!("</svg>");
}
