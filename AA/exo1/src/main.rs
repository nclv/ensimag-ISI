
fn remise_a_zero(tranche: &mut [i32]) {
    for x in tranche {
        *x = 0;
    }
}

fn main() {
    let v1 = vec![1, 2, 3, 4, 5];
    println!("v1 est {:?}", v1);

    let mut s = 0;
    for x in &v1 {
        s += *x;
    }
    println!("la somme vaut {}", s);

    let mut v2 = vec![0; 5];
    println!("v2 est {:?}", v2);

    for x in 1..6 {
        v2[x - 1] = x as i32;
    }
    assert_eq!(v1, v2);

    remise_a_zero(v2.as_mut_slice());
    println!("que des 0: {:?}", v2);
}
