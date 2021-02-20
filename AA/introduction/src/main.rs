fn clone_test() {
    // Clone
    let x = String::from("Hello World");
    let y = x.clone();
    println!("x={}, y={}", x, y);
}

fn copy_trait() {
    // The type implements copy trait
    let x = 3;
    let y = x;
    println!("x={}, y={}", x, y);
}

fn append_newline(original: String) -> String {
    // pure function
    let mut result = original;
    result.push_str("\n");
    result
}

fn test_append_newline() {
    let x = String::from("Hello World");
    // the function took ownership of x
    let y = append_newline(x);
    println!("y={}", y);
}

fn len(s: &String) -> usize {
    s.len()
}

fn references() {
    let x = String::from("Hello World");
    // we couldn't use x after the call to len(x) if we didn't use references
    println!("{}", len(&x));
    println!("{}", x);
}

enum Void {}
// 1 value, or ()
enum Unit {
    Unit,
}
// enum is a sum type: 1 + 1, or bool
enum Direction {
    Up,
    Down,
}
// 1 + A
enum OptionRedefined<A> {
    Some(A),
    None,
}
// A + B
enum ResultRedefined<A, B> {
    Ok(A),
    Err(B),
}
// A * B
// (A, B)
// struct Tuple {
//     a: A,
//     b: B,
// }
// L = 1 + AL or linked list
// Cons is a variant of the List enum. It's saying there are two possible cases of a linked list - an empty list or a head consisting of a u32 and a ~List
// Box tell it is allocated on the heap
enum List<A> {
    Nil,
    Cons(A, Box<List<A>>),
}

struct Person {
    name: String,
    address: Option<String>,
}

fn pattern_matching() {
    let person = Person {
        name: String::from("Nils"),
        address: None, // Some(String::from("Address")),
    };

    let (name, address) = match person {
        Person {
            name,
            address: Some(s),
        } => (name, s.len()),
        Person {
            name,
            address: None,
        } => (name, 0),
    };
    println!("{}, {}", name, address);
}

fn age_type(age: Option<i32>) -> &'static str {
    match age {
        Some(val) if val < 0 => "Negative",
        Some(_val @ 0..=18) => "Less than 18",
        Some(val) if val > 150 => "Greater than 150",
        Some(_val) => "Adult",
        None => "Empty",
    }
}

use chrono::Duration;
use std::{num::ParseIntError, ops, vec};

#[derive(Debug)]
struct Point(i64, i64);

impl ops::Add<Point> for Point {
    type Output = Point;
    fn add(self, other: Point) -> Self::Output {
        Point(self.0 + other.0, self.1 + other.1)
    }
}

pub trait TimeDuration {
    fn days(&self) -> Duration;
}

impl TimeDuration for i64 {
    fn days(&self) -> Duration {
        Duration::days(*self)
    }
}

fn factorial1(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => n * factorial1(n - 1),
    }
}

fn factorial2(n: u64) -> u64 {
    (1..n + 1).fold(1, |acc, i| acc * i)
}

fn factorial3(n: u64) -> u64 {
    (1..n + 1).fold(1, ops::Mul::mul)
}

fn factorial4(n: u64) -> u64 {
    (1..n + 1).product()
}

struct MyVec<T> {
    // ptr: Unique<T>,
    // cap: usize,
    // len: usize,
    vec: Vec<T>,
}

impl<T> MyVec<T> {
    pub fn find<P>(&self, predicate: P) -> Option<&T>
    where
        P: Fn(&T) -> bool,
    {
        for v in &self.vec {
            if predicate(v) {
                return Some(v);
            }
        }
        None
    }
}

fn test_my_vec() {
    let my_vect = MyVec {
        vec: vec![1, 2, 33],
    };
    if let Some(f) = my_vect.find(|t| t >= &32) {
        println!("{}", f);
    }
}

enum DecompressionResult {
    Finished { size: u32 },
    InputError(std::io::Error),
    OutputError(std::io::Error),
}

// match decompress() {
//     Finished {size} => { /* Parsed successfully */ }
//     InputError(e) if e.is_eof() => { /* EOF error */ }
//     OutputError(e) => { /* output failed with error e */ }
// }

#[test]
fn it_works() {
    assert_eq!(1 + 1, 2);
}

/// Return one more
///
/// ```
/// assert_eq!(one_more(42), 43);
/// ```
pub fn one_more(n: i32) -> i32 {
    n + 1
}

// every value has an owner, responsible for destructor (RAII)
// only ever one owner: no double-free
// let x = Vec::new();
// let y = x;
// drop(x); // illegal, y is now owner

// no pointers live pas owner changes or drops:
// no dangling pointers/use-after-free
// let mut x = vec![1, 2, 3];
// let first = &x[0];
// let y = x;
// println!("{}", *first); // illegal, first became invalid when x was moved

use std::rc::Rc; // reference-counted, non atomic
use std::sync::Arc; // reference-counted, atomic

fn test_threads() {
    // let rc = Rc::new("not thread safe");
    // std::thread::spawn(move || {
    //     println!("I have an rc with: {}", rc);
    // });

    let arc = Arc::new("tread safe");
    std::thread::spawn(move || {
        println!("I have an arc with: {}", arc);
    });

    // only one mutable reference or any number of mutable references to any value
    // one writer or many readers
    // let mut v = Vec::new();
    // std::thread::spawn(|| {
    //     v.push(42);
    // });
    // let _ = v.pop();
}

fn states() -> Result<i32, ParseIntError> {
    let my_vect = MyVec {
        vec: vec![1, 2, 33],
    };
    // v is Option<&T>, not &T -- cannot use without checking for None
    let v = my_vect.find(|t| t >= &32);
    // n is Result<i32, ParseIntError> -- cannot use without checking for Err
    let n = "42".parse::<i32>();
    // ? suffix is "return Err if Err, otherwise unwrap Ok"
    let n: i32 = "42".parse()?;
    Ok(n)
}

fn try_to_parse() -> Result<i32, ParseIntError> {
    let x: i32 = "123".parse()?; // x = 123
    let y: i32 = "24a".parse()?; // returns an Err() immediately
    Ok(x + y)                    // Doesn't run.
}

fn heap() {
    // variables are all on the stack
    let x = 42;
    let z = [0; 1024];

    // heap allocation
    let heap_x = Box::new(x);
    let heap_z = vec![0; 1024];
}

fn main() {
    clone_test();
    copy_trait();
    test_append_newline();
    references();
    pattern_matching();
    age_type(Some(17));
    println!("{:?}", Point(1, 2) + Point(2, 1));
    println!("{:?}", 3.days());
    println!("{}", factorial1(4));
    println!("{}", factorial2(4));
    println!("{}", factorial3(4));
    println!("{}", factorial4(4));
    test_my_vec();
    states();
    let res = try_to_parse();
    println!("{:?}", res);
    heap();
}
