public class TestZoo {
    public static void main(String[] args) {
        Zoo ensimagZoo = new Zoo("Ensimag");

        ensimagZoo.ajouteAnimal(new Animal("Catherine", 23));
        ensimagZoo.ajouteAnimal(new Animal("Julie", 30));
        ensimagZoo.ajouteAnimal(new Animal("Sahar", 59));
        ensimagZoo.ajouteAnimal(new Animal("Benoit", 45));
        ensimagZoo.ajouteAnimal(new Animal("Nicolas", 46));
        ensimagZoo.ajouteAnimal(new Animal("Sebastien", 37));
        ensimagZoo.ajouteAnimal(new Animal("Sylvain", 98));

        System.out.println(ensimagZoo.toString());
    }
}
