#![warn(clippy::all)]
#[derive(Debug)]
enum Couleur {
    Rouge,
    Vert,
    Bleu,
}

#[derive(Debug)]
struct Point {
    x: f64,
    y: f64,
    couleur: Option<Couleur>,
}

impl Point {
    fn new(x: f64, y: f64) -> Point {
        Point {
            x,
            y,
            couleur: None,
        }
    }
    fn distance_a(&self, autre: &Self) -> f64 {
        ((self.x - autre.x).powi(2) + (self.y - autre.y).powi(2)).sqrt()
    }
}

fn main() {
    let p1 = Point {
        x: 0.0,
        y: 0.0,
        couleur: Some(Couleur::Rouge),
    };
    println!("p1: {:?}", p1);
    let p2 = Point::new(2.0, 2.0);
    println!("p2: {:?}", p2);
    println!("distance entre p1 et p2: {}", p1.distance_a(&p2));
}
