/**
 * Rational
 */
public class Rational {

    private int numerator, denominator;

    public Rational() {
        this(0, 1);
    }

    /**
     * Initializes a newly created Rational with the value n/1.
     * 
     * @param numerator numerator
     */
    public Rational(int numerator) {
        this(numerator, 1);
    }

    /**
     * Initializes a newly created Rational with the value num/denom, then
     * simplifies this rational.
     *
     * @param numerator   numerator
     * @param denominator denominator
     * @throws ArithmeticException if denom is zero
     */
    public Rational(int numerator, int denominator) {
        if (denominator == 0) {
            throw new ArithmeticException("Denominator is zero.");
        }
        this.denominator = denominator;
        this.numerator = numerator;
        reduce();
    }

    private void reduce() {
        // reduce fraction
        int g = Rational.gcd(this.numerator, this.denominator);
        this.numerator /= g;
        this.denominator /= g;
        if (this.denominator < 0) {
            this.numerator = -this.numerator;
            this.denominator = -this.denominator;
        }
    }

    /**
     * Copy constructor: initializes the newly created Rational with the numerator
     * and denominator of the argument.
     */
    public Rational(Rational other) {
        this(other.numerator, other.denominator);
    }

    // return the numerator and denominator of (this)
    public int getNumerator() {
        return this.numerator;
    }

    public int getDenominator() {
        return this.denominator;
    }

    /**
     * Sets the numerator, then simplifies the rational.
     * @param n new numerator value
     */	
    public void setNum(int n) {
        this.numerator = n;
        reduce();
    }

    /**
     * Sets the denominator, then simplifies the rational.
     * @param denominator new denominator value
     * @throws ArithmeticException if d is zero 
     */	
    public void setDenom(int denominator) {
        if (denominator == 0) {
            throw new ArithmeticException("Division by zero...");
        }
        this.denominator = denominator;
        reduce();
    }

    /**
     * Converts this rational value to double.
     * 
     * @return the double floating point value closest to the rational value
     *         represented by this rational.
     */
    public double getValue() {
        return (double) this.numerator / this.denominator;
    }

    /**
     * Multiplies this with b, then simplifies the rational reducing overflow risk.
     */
    public Rational mult(Rational b) {
        Rational a = this;

        // reduce p1/q2 and p2/q1, then multiply, where a = p1/q1 and b = p2/q2
        Rational c = new Rational(a.numerator, b.denominator);
        Rational d = new Rational(b.numerator, a.denominator);

        return new Rational(c.numerator * d.numerator, c.denominator * d.denominator);
        // OR
        // return new Rational(this.numerator * b.numerator, this.denominator *
        // b.denominator);
    }

    /**
     * Multiplies two rationals, then returns the result.
     * This a class method, used this way:
     *     Rational res = Rational.mult(a, b); 
     */
    public static Rational mult(Rational a, Rational b) {
    	Rational c = new Rational(a.numerator, b.denominator);
        Rational d = new Rational(b.numerator, a.denominator);

        return new Rational(c.numerator * d.numerator, c.denominator * d.denominator);
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
        return this.mult(b.reciprocal());
    }

    @Override
    public boolean equals(Object o) {
        return (o instanceof Rational) && (((Rational) o).getNumerator() == this.getNumerator())
                && (((Rational) o).getDenominator() == this.getDenominator());
    }

    /** return string representation of (this) */
    @Override
    public String toString() {
        if (this.denominator == 1)
            return this.numerator + "";
        else
            return this.numerator + "/" + this.denominator;
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