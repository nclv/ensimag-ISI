public class TestRational {
    public static void main(String[] args) {
        Rational x, y, z;

        // 1/2 + 1/3 = 5/6
        x = new Rational(1, 2);
        y = new Rational(1, 3);
        z = x.add(y);
        System.out.println(z);

        // 8/9 + 1/9 = 1
        x = new Rational(8, 9);
        y = new Rational(1, 9);
        z = x.add(y);
        System.out.println(z);

        // 4/17 * 7/3 = 28/51
        x = new Rational(4, 17);
        y = new Rational(7, 3);
        z = x.times(y);
        System.out.println(z);

        // 203/16957 * 9299/5887 = 17/899
        x = new Rational(203, 16957);
        y = new Rational(9299, 5887);
        z = x.times(y);
        System.out.println(z);

        // 0/6 = 0
        x = new Rational(0, 6);
        System.out.println(x);

    }
}
