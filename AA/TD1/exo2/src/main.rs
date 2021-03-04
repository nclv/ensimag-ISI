#![warn(clippy::all)]
fn main() {
    let r: Vec<_> = (1..21).collect();
    println!("r: {:?}", r);
    let s: Vec<_> = (1..21).rev().collect();
    println!("s: {:?}", s);
    let mut t = Vec::new();
    for (x, y) in r.iter().zip(s.iter()) {
        t.push(x + y);
    }
    println!("vecteur somme: {:?}", t);

    let t: Vec<_> = r.iter().zip(s.iter()).map(|(x, y)| x + y).collect();
    println!("vecteur somme: {:?}", t);

    println!("tout est 21: {}", t.iter().all(|x| *x == 21));
    let somme: i32 = r.iter().sum();
    println!("la somme de r est {}", somme);

    let u: Vec<_> = (1..11).map(|x| x * x).collect();
    println!("u: {:?}", u);
}
