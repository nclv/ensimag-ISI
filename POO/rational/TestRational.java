package rational;

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
        z = x.mult(y);
        System.out.println(z);

        // 203/16957 * 9299/5887 = 17/899
        x = new Rational(203, 16957);
        y = new Rational(9299, 5887);
        z = x.mult(y);
        System.out.println(z);

        // 0/6 = 0
        x = new Rational(0, 6);
        System.out.println(x);

        Rational r = new Rational(6, 4);
        System.out.println("r = " + r);
        System.out.println("\tas double, r = " + r.getValue());

        Rational s = new Rational(2);
        System.out.println("s = " + s);

        r = r.add(s);
        System.out.println("r + s = " + r);
        
        Rational t = new Rational(34, 8);
        System.out.println("t = " + t + " (17/4 if reduced)");
        
        Rational st = Rational.mult(s, t);
        System.out.println("st = " + st + " (17/2 if reduced)");
    }
}
