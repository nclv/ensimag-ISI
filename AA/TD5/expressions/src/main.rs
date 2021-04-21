#![warn(clippy::all)]
use rayon::prelude::*;

#[derive(Debug)]
enum Token {
    Plus,
    Fois,
    Entier(u32),
}

fn evaluation_simple(expression: &[Token]) -> u32 {
    expression
        .par_split(|t| match *t {
            Token::Plus => true,
            _ => false,
        })
        .map(|s| {
            s.iter()
                .filter_map(|t| match *t {
                    Token::Entier(i) => Some(i),
                    _ => None,
                })
                .product::<u32>()
        })
        .sum()
}

fn main() {
    let expression = vec![
        Token::Entier(1),
        Token::Plus,
        Token::Entier(3),
        Token::Fois,
        Token::Entier(5),
        Token::Fois,
        Token::Entier(2),
        Token::Plus,
        Token::Entier(1),
    ];
    println!("{:?} = {}", expression, evaluation_simple(&expression));
}
