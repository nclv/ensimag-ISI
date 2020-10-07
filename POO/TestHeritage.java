public class TestHeritage {
    public static void main(String[] args) {
        Canard donald = new Canard("Canardo", 5, "noir tuxien");
        Animal tux = donald;

        System.out.println("Faisons crier Donald deux fois... ");
        donald.crier();
        tux.crier();

        System.out.println("Oh les belles plumes " +
            donald.getCouleurPlumes());
        // System.out.println("Oh les belles plumes. " +
        //     tux.getCouleurPlumes());

        /***************/
        Vache marguerite = new Vache("Marguerite", 243, 17);
        Animal unAnimal = marguerite;

        unAnimal = new Vache("Kyrie", 332, 3);
        // un genre de vache guerrière qui sent le fromage
        Vache kyrie = (Vache) unAnimal;

        unAnimal = new Animal("Kyrie", 332);
        kyrie = (Vache) unAnimal;
    }
}
