extern crate rayon;
extern crate time;
extern crate rand;

use std::ops::Range;
//use rayon::prelude::*;
use rayon::join;
use rand::random;
use time::PreciseTime;

fn bench<F>(label: &str, f: F)
    where F: Fn()
{
    let start = PreciseTime::now();
    f();
    let end = PreciseTime::now();
    println!("{} took {}", label, start.to(end));
}

// renvoie l'indice de debut de la plus grande plage
// d'elements identiques
fn seq_range<T: Eq>(slice: &[T]) -> (usize, usize) {
    let mut best_index = 0;
    let mut best_count = 1;

    let mut elements = slice.iter().enumerate();
    let (mut start_index, mut prec) = elements.next().unwrap();
    let mut count = 1;

    for (index, e) in elements {
        if e == prec {
            count += 1;
            if count > best_count {
                best_count = count;
                best_index = start_index;
            }
        } else {
            count = 1;
            start_index = index;
        }
        prec = e;
    }
    (best_index, best_count)
}

fn count_last_element<T: Eq>(slice: &[T]) -> usize {
    let last = slice.last().unwrap();
    let mut count = 0;
    for e in slice.iter().rev() {
        if e == last {
            count += 1;
        } else {
            return count;
        }
    }
    count
}

fn count_first_element<T: Eq>(slice: &[T]) -> usize {
    let first = slice.first().unwrap();
    let mut count = 0;
    for e in slice {
        if e == first {
            count += 1;
        } else {
            return count;
        }
    }
    count
}

fn dc1_range<T: Eq + Sync>(slice: &[T]) -> (usize, usize) {
    if slice.len() <= 4 {
        seq_range(slice)
    } else {
        let middle = slice.len() / 2;
        let (lo, hi) = slice.split_at(middle);
        let mut r1 = (0, 0);
        let mut r2 = (0, 0);
        join(|| r1 = dc1_range(lo), || r2 = dc1_range(hi));

        let (middle_count, middle_start) = if lo.last().unwrap() == hi.first().unwrap() {
            let count_last = count_last_element(lo);
            let count_first = count_first_element(hi);
            (count_last + count_first, lo.len() - count_last)
        } else {
            (0, 0)
        };

        let counts = [r2.1, middle_count, r1.1];
        let starts = [r2.0 + lo.len(), middle_start, r1.0];
        let (s, m) = starts.iter()
            .zip(counts.iter())
            .max_by_key(|&(_, c)| c)
            .unwrap();
        (*s, *m)
    }
}

fn seq_range2<T: Eq>(slice: &[T]) -> [Range<usize>; 3] {
    let mut elements = slice.iter().enumerate();
    let (start_index, mut previous) = elements.next().unwrap();
    let mut current_range = start_index..(start_index + 1);
    let mut best_range = 0..1;
    let mut start_range = 0..1;

    for (index, e) in elements {
        if e == previous {
            current_range.end = index + 1;
            if current_range.len() > best_range.len() {
                if best_range.start == 0 {
                    start_range = best_range.clone();
                }
                best_range = current_range.clone();
            }
        } else {
            current_range = index..(index + 1);
        }
        previous = e;
    }
    if best_range.start == 0 {
        start_range = best_range.clone();
    }
    [start_range, best_range, current_range]
}



fn best_range<T: Eq + Sync + std::fmt::Debug>(slice: &[T]) -> (usize, usize) {
    fn dc2<T: Eq + Sync + std::fmt::Debug>(slice: &[T], min_size: usize) -> [Range<usize>; 3] {
        if slice.len() <= min_size {
            seq_range2(slice)
        } else {
            let middle = slice.len() / 2;
            let (left_slice, right_slice) = slice.split_at(middle);
            let mut left_ranges = [0..0, 0..0, 0..0];
            let mut right_ranges = [0..0, 0..0, 0..0];
            join(|| left_ranges = dc2(left_slice, min_size),
                 || right_ranges = dc2(right_slice, min_size));
            let middle_range = if left_slice.last().unwrap() == right_slice.first().unwrap() {
                left_ranges[2].start..(right_ranges[0].end + left_slice.len())
            } else {
                0..0
            };
            for range in &mut right_ranges {
                range.start += left_slice.len();
                range.end += left_slice.len();
            }
            let candidates_ranges = [&left_ranges[1], &middle_range, &right_ranges[1]];
            [left_ranges[0].clone(),
             (*candidates_ranges.iter()
                   .rev()
                   .max_by_key(|r| r.len())
                   .unwrap())
                     .clone(),
             right_ranges[2].clone()]
        }
    }

    let min_size = (slice.len() as f64).ln().ceil() as usize;
    let ranges = dc2(slice, min_size);
    (ranges[1].start, ranges[1].end - ranges[1].start)
}

fn main() {
    let t: Vec<_> = (0..1000).into_iter().map(|_| random::<u32>() % 3).collect();
    //let t: Vec<_> = (0..10000000).into_iter().map(|_| random::<u32>() % 3).collect();
    println!("array: {:?}", t);
    let (start, size) = seq_range(&t);
    println!("best range starts at {} with a length of {}", start, size);
    let (start, size) = dc1_range(&t);
    println!("best range starts at {} with a length of {}", start, size);
    let (start, size) = best_range(&t);
    println!("best range starts at {} with a length of {}", start, size);
    bench("sequential", || { seq_range(&t); });
    bench("parallel1", || { dc1_range(&t); });
    bench("parallel2", || { best_range(&t); });
}
