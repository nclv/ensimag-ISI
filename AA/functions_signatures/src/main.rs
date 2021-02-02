// VISIBILITY
mod visibility {
    fn private_function() {}
    pub fn public_function() {}
}

// Optional to avoid `visibility::`
use visibility::public_function;
// If you have a function like foo::bar::baz::rad() in your project and want to make it usable as foo::rad() add pub use bar::baz::rad; to your foo module. This is called re-exporting.

// BORROWING
struct Dog {
    name: String,
    walked: bool,
}
struct Bear {
    walked: bool,
}

// The Self return type which represents the current type.
// The self parameter which specifies the borrowing/moving/mutability of the structure instance. In walk() below we take a mutable borrow, a bare self moves the value.
impl Dog {
    pub fn adopt(name: String) -> Self {
        Dog {
            name: name,
            walked: false,
        }
    }
    pub fn walk(&mut self) {
        self.walked = true
    }
}

fn walk_dog(dog: &mut Dog) {
    dog.walked = true;
}

// Note that the name is moved in and given to the dog, not copied or cloned.
fn adopt_dog(name: String) -> Dog {
    Dog {
        name: name,
        walked: false,
    }
}

// GENERICS
// The important thing to note about generics is when you're accepting a generic you may only use the functions from the constraints. This means that if you pass a Read to a function that wants Write, it still can't Read in it unless the constraints include it.
trait Walk {
    fn walk(&mut self);
}
impl Walk for Dog {
    fn walk(&mut self) {
        self.walked = true
    }
}
impl Walk for Bear {
    fn walk(&mut self) {
        self.walked = true
    }
}

fn walk_pet<W: Walk>(pet: &mut W) {
    // Try setting `pet.walked` here!
    // You can't!
    pet.walk();
}

fn walk_pet_2(pet: &mut dyn Walk) {
    // Try setting `pet.walked` here!
    // You can't!
    pet.walk();
}

fn walk_pet_3<W>(pet: &mut W)
where W: Walk {
    pet.walk();
}

// If you have multiple generics you can comma seperate them in both cases. If you'd like more than one trait contraint you can use where W: Walk + Read or <W: Walk + Read>.
// fn stuff<R, W>(r: &R, w: &mut W)
// where W: Write, R: Read + Clone {}

// PASSING FUNCTIONS
fn do_with<F>(dog: &mut Dog, action: F)
where F: Fn(&mut Dog) {
    action(dog);
}

fn main() {
    let x = 3;
    println!("Hello, world!");
    println!("{x}", x = x);

    // VISIBILITY
    visibility::public_function();
    // With `use`
    public_function();

    // BORROWING
    // Values with Copy are implictly copied when passed to functions. You can make something Copy by adding #[derive(Copy)] above the declaration.
    // We could clone rover. But our Dog struct isn't Clone either! Clone means we can explicitly make a copy of an object. You can make something Clone just like you did as Copy. To clone our dog you can do rover.clone()
    let mut rover = Dog::adopt(String::from("Bob")); // adopt_dog(String::from("Bob"));
    assert_eq!(rover.name, "Bob");
    // walk_dog(&mut rover);
    rover.walk();
    assert_eq!(rover.walked, true);

    // GENERICS
    // When being written in a signature you want to use something like Iterator<Item=Dog> to say an iterator of Dogs.

    // PASSING FUNCTIONS
    // Functions in Rust implement traits which determine where (and how) they are passed:
    // FnOnce - Takes a by-value reciever.
    // FnMut - Takes a mutable reciever.
    // Fn - Takes a immutable reciever.
    
    // All closures implement FnOnce: a closure that can't be called once doesn't deserve the name. Note that if a closure only implements FnOnce, it can be called only once.
    // Closures that don't move out of their captures implement FnMut, allowing them to be called more than once (if there is unaliased access to the function object).
    // Closures that don't need unique/mutable access to their captures implement Fn, allowing them to be called essentially everywhere.

    // Fn
    do_with(&mut rover, walk_pet);
    // Closure
    do_with(&mut rover, |dog| dog.walked = true);
}
