/**
 * Rational
 */
public class Rational {

    private int numerator, denominator;

    public Rational() {
        this(0, 1);
    }

    public Rational(int numerator) {
        this(numerator, 1);
    }

    public Rational(int numerator, int denominator) {
        if (denominator == 0) {
            throw new ArithmeticException("Denominator is zero.");
        }
        // reduce fraction
        int g = gcd(numerator, denominator);
        this.numerator = numerator / g;
        this.denominator = denominator / g;
    }

    // return the numerator and denominator of (this)
    public int numerator() {
        return this.numerator;
    }

    public int denominator() {
        return this.denominator;
    }

    public float getValue() {
        return this.numerator / (float) this.denominator;
    }

    // return string representation of (this)
    public String toString() {
        if (this.denominator == 1)
            return this.numerator + "";
        else
            return this.numerator + "/" + this.denominator;
    }

    // return (this * b), reduce overflow risk
    public Rational times(Rational b) {
        Rational a = this;

        // reduce p1/q2 and p2/q1, then multiply, where a = p1/q1 and b = p2/q2
        Rational c = new Rational(a.numerator, b.denominator);
        Rational d = new Rational(b.numerator, a.denominator);
        return new Rational(c.numerator * d.numerator, c.denominator * d.denominator);
        // OR
        // return new Rational(this.numerator * b.numerator, this.denominator *
        // b.denominator);
    }

    // return (this + b)
    public Rational add(Rational b) {
        int numerator = (this.numerator * b.denominator) + (this.denominator * b.numerator);
        int denominator = this.denominator * b.denominator;
        return new Rational(numerator, denominator);
    }

    // return (1 / this)
    public Rational reciprocal() {
        return new Rational(this.denominator, this.numerator);
    }

    // return (this / b)
    public Rational divides(Rational b) {
        return this.times(b.reciprocal());
    }

    public boolean equals(Rational that) {
        return this.numerator == that.numerator && this.denominator == that.denominator;
    }

    // return gcd(|m|, |n|)
    private static int gcd(int m, int n) {
        if (m < 0)
            m = -m;
        if (n < 0)
            n = -n;
        if (0 == n)
            return m;
        else
            return gcd(n, m % n);
    }
}