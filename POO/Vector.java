public class Vector {
    /**
     * The internal array used to hold members of a Vector. The elements are in
     * positions 0 through elementCount - 1, and all remaining slots are null.
     * 
     * @serial the elements
     */
    protected Rational[] rationals;

    /**
     * The number of elements currently in the vector, also returned by
     * {@link #size}.
     * 
     * @serial the size
     */

    protected int rationalCount;
    protected static final int INITIAL_CAPACITY = 10;

    

    /**
     * s The amount the Vector's internal array should be increased in size when a
     * new element is added that exceeds the current size of the array, or when
     * {@link #ensureCapacity} is called. If &lt;= 0, the vector just doubles in
     * size.
     * 
     * @serial the amount to grow the vector by
     */

    protected int capacityIncrement;

    /**
     * Constructs an empty vector with an initial size of 10, and a capacity
     * increment of 0
     */
    public Vector() {
        this(INITIAL_CAPACITY, 0);
    }

    /**
     * Constructs a Vector with the initial capacity specified, and a capacity
     * increment of 0 (double in size).
     *
     * @param initialCapacity the initial size of the Vector's internal array
     * @throws IllegalArgumentException if initialCapacity &lt; 0
     */
    public Vector(int initialCapacity) {
        this(initialCapacity, 0);
    }

    /**
     * Constructs a Vector with the initial capacity and capacity increment
     * specified.
     *
     * @param initialCapacity   the initial size of the Vector's internal array
     * @param capacityIncrement the amount the internal array should be increased by
     *                          when necessary, 0 to double the size
     * @throws IllegalArgumentException if initialCapacity &lt; 0
     */
    public Vector(int initialCapacity, int capacityIncrement) {
        if (initialCapacity < 0)
            throw new IllegalArgumentException();
        rationals = new Rational[initialCapacity];
        this.capacityIncrement = capacityIncrement;
    }

    /**
     * Constructs a vector containing the contents of Array, in order.
     *
     * @param c collection of elements to add to the new vector
     * @throws NullPointerException if c is null
     * @since 1.2
     */
    public Vector(Rational[] rationals) {
        this.rationals = rationals.clone();
        this.rationalCount = rationals.length;
        ensureCapacity(2 * rationals.length);
    }

    /**
     * Ensures that minCapacity elements can fit within this Vector. If rationals is
     * too small, it is expanded as foll If the rationalCount + capacityIncrement is
     * adequate, that is the new size. If capacityIncrement is non-zero, the
     * candidate size is double the current. If that is not enough, the new size is
     * minCapacity.
     *
     * @param minCapacity the desired minimum capacity, negative values ignored
     */
    public void ensureCapacity(int minCapacity) {
        if (rationals.length >= minCapacity)
            return;

        int newCapacity;
        if (capacityIncrement <= 0)
            newCapacity = rationals.length * 2;
        else
            newCapacity = rationals.length + capacityIncrement;

        Rational[] newArray = new Rational[Math.max(newCapacity, minCapacity)];

        System.arraycopy(rationals, 0, newArray, 0, rationalCount);
        rationals = newArray;
    }

    /**
     * Returns true when elem is contained in this Vector.
     *
     * @param elem the element to check
     * @return true if the rational is contained in this Vector, false otherwise
     */
    public boolean contains(Rational elem) {
        return indexOf(elem, 0) >= 0;
    }

    /**
     * Returns the first occurrence of elem in the Vector, or -1 if
     * elem is not found.
     *
     * @param elem the rational to search for
     * @return the index of the first occurrence, or -1 if not found
     */
    public int indexOf(Rational elem) {
        return indexOf(elem, 0);
    }

    /**
     * Searches the vector starting at index for Rational
     * elem and returns the index of the first occurrence of this
     * Rational. If the Rational is not found, or index is larger than the size of the
     * vector, -1 is returned.
     *
     * @param e     the Rational to search for
     * @param index start searching at this index
     * @return the index of the next occurrence, or -1 if it is not found
     * @throws IndexOutOfBoundsException if index &lt; 0
     */
    public int indexOf(Rational e, int index) {
        for (int i = index; i < rationalCount; i++)
            if (e.equals(rationals[i]))
                return i;
        return -1;
    }

    /**
     * Returns the size of the internal data array (not the amount of elements
     * contained in the Vector).
     *
     * @return capacity of the internal data array
     */
    public int capacity() {
        return rationals.length;
    }

    /**
     * Returns the number of elements stored in this Vector.
     *
     * @return the number of elements in this Vector
     */
    public int size() {
        return rationalCount;
    }

    /**
     * Returns true if this Vector is empty, false otherwise
     *
     * @return true if the Vector is empty, false otherwise
     */
    public boolean isEmpty() {
        return rationalCount == 0;
    }

    // return string representation of (this)
    public String toString() {
        String s = "(";
        for (int i = 0; i < this.rationalCount; ++i) {
            s += this.rationals[i] + ", ";
        }
        return s + ")";
    }

    public static void main(String[] args) {
        Rational a = new Rational(1, 2);
        Rational b = new Rational(3, 2);
        Rational[] rationals = { a, b };
        Vector vect = new Vector(rationals);
        System.out.println(vect);
        System.out.println(vect.size());
        System.out.println(vect.capacity());
        System.out.println(vect.contains(a));
    }
}
