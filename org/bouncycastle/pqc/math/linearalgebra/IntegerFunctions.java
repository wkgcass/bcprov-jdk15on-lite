package org.bouncycastle.pqc.math.linearalgebra;

import java.math.BigInteger;
import java.security.SecureRandom;

import org.bouncycastle.crypto.CryptoServicesRegistrar;
import org.bouncycastle.util.BigIntegers;

/**
 * Class of number-theory related functions for use with integers represented as
 * <tt>int</tt>'s or <tt>BigInteger</tt> objects.
 */
public final class IntegerFunctions
{

    private static final BigInteger ZERO = BigInteger.valueOf(0);

    private static final BigInteger ONE = BigInteger.valueOf(1);

    private static final BigInteger TWO = BigInteger.valueOf(2);

    private static final BigInteger FOUR = BigInteger.valueOf(4);

    private static final int[] SMALL_PRIMES = {3, 5, 7, 11, 13, 17, 19, 23,
        29, 31, 37, 41};

    private static final long SMALL_PRIME_PRODUCT = 3L * 5 * 7 * 11 * 13 * 17
        * 19 * 23 * 29 * 31 * 37 * 41;

    private static SecureRandom sr = null;

    // the jacobi function uses this lookup table
    private static final int[] jacobiTable = {0, 1, 0, -1, 0, -1, 0, 1};

    private IntegerFunctions()
    {
        // empty
    }

    /**
     * Computes the value of the Jacobi symbol (A|B). The following properties
     * hold for the Jacobi symbol which makes it a very efficient way to
     * evaluate the Legendre symbol
     * <p>
     * (A|B) = 0 IF gcd(A,B) &gt; 1<br>
     * (-1|B) = 1 IF n = 1 (mod 1)<br>
     * (-1|B) = -1 IF n = 3 (mod 4)<br>
     * (A|B) (C|B) = (AC|B)<br>
     * (A|B) (A|C) = (A|CB)<br>
     * (A|B) = (C|B) IF A = C (mod B)<br>
     * (2|B) = 1 IF N = 1 OR 7 (mod 8)<br>
     * (2|B) = 1 IF N = 3 OR 5 (mod 8)
     *
     * @param A integer value
     * @param B integer value
     * @return value of the jacobi symbol (A|B)
     */
    public static int jacobi(BigInteger A, BigInteger B)
    {
        BigInteger a, b, v;
        long k = 1;

        k = 1;

        // test trivial cases
        if (B.equals(ZERO))
        {
            a = A.abs();
            return a.equals(ONE) ? 1 : 0;
        }

        if (!A.testBit(0) && !B.testBit(0))
        {
            return 0;
        }

        a = A;
        b = B;

        if (b.signum() == -1)
        { // b < 0
            b = b.negate(); // b = -b
            if (a.signum() == -1)
            {
                k = -1;
            }
        }

        v = ZERO;
        while (!b.testBit(0))
        {
            v = v.add(ONE); // v = v + 1
            b = b.divide(TWO); // b = b/2
        }

        if (v.testBit(0))
        {
            k = k * jacobiTable[a.intValue() & 7];
        }

        if (a.signum() < 0)
        { // a < 0
            if (b.testBit(1))
            {
                k = -k; // k = -k
            }
            a = a.negate(); // a = -a
        }

        // main loop
        while (a.signum() != 0)
        {
            v = ZERO;
            while (!a.testBit(0))
            { // a is even
                v = v.add(ONE);
                a = a.divide(TWO);
            }
            if (v.testBit(0))
            {
                k = k * jacobiTable[b.intValue() & 7];
            }

            if (a.compareTo(b) < 0)
            { // a < b
                // swap and correct intermediate result
                BigInteger x = a;
                a = b;
                b = x;
                if (a.testBit(1) && b.testBit(1))
                {
                    k = -k;
                }
            }
            a = a.subtract(b);
        }

        return b.equals(ONE) ? (int)k : 0;
    }

    /**
     * Computes the square root of a BigInteger modulo a prime employing the
     * Shanks-Tonelli algorithm.
     *
     * @param a value out of which we extract the square root
     * @param p prime modulus that determines the underlying field
     * @return a number <tt>b</tt> such that b<sup>2</sup> = a (mod p) if
     *         <tt>a</tt> is a quadratic residue modulo <tt>p</tt>.
     * @throws IllegalArgumentException if <tt>a</tt> is a quadratic non-residue modulo <tt>p</tt>
     */
    public static BigInteger ressol(BigInteger a, BigInteger p)
        throws IllegalArgumentException
    {

        BigInteger v = null;

        if (a.compareTo(ZERO) < 0)
        {
            a = a.add(p);
        }

        if (a.equals(ZERO))
        {
            return ZERO;
        }

        if (p.equals(TWO))
        {
            return a;
        }

        // p = 3 mod 4
        if (p.testBit(0) && p.testBit(1))
        {
            if (jacobi(a, p) == 1)
            { // a quadr. residue mod p
                v = p.add(ONE); // v = p+1
                v = v.shiftRight(2); // v = v/4
                return a.modPow(v, p); // return a^v mod p
                // return --> a^((p+1)/4) mod p
            }
            throw new IllegalArgumentException("No quadratic residue: " + a + ", " + p);
        }

        long t = 0;

        // initialization
        // compute k and s, where p = 2^s (2k+1) +1

        BigInteger k = p.subtract(ONE); // k = p-1
        long s = 0;
        while (!k.testBit(0))
        { // while k is even
            s++; // s = s+1
            k = k.shiftRight(1); // k = k/2
        }

        k = k.subtract(ONE); // k = k - 1
        k = k.shiftRight(1); // k = k/2

        // initial values
        BigInteger r = a.modPow(k, p); // r = a^k mod p

        BigInteger n = r.multiply(r).remainder(p); // n = r^2 % p
        n = n.multiply(a).remainder(p); // n = n * a % p
        r = r.multiply(a).remainder(p); // r = r * a %p

        if (n.equals(ONE))
        {
            return r;
        }

        // non-quadratic residue
        BigInteger z = TWO; // z = 2
        while (jacobi(z, p) == 1)
        {
            // while z quadratic residue
            z = z.add(ONE); // z = z + 1
        }

        v = k;
        v = v.multiply(TWO); // v = 2k
        v = v.add(ONE); // v = 2k + 1
        BigInteger c = z.modPow(v, p); // c = z^v mod p

        // iteration
        while (n.compareTo(ONE) == 1)
        { // n > 1
            k = n; // k = n
            t = s; // t = s
            s = 0;

            while (!k.equals(ONE))
            { // k != 1
                k = k.multiply(k).mod(p); // k = k^2 % p
                s++; // s = s + 1
            }

            t -= s; // t = t - s
            if (t == 0)
            {
                throw new IllegalArgumentException("No quadratic residue: " + a + ", " + p);
            }

            v = ONE;
            for (long i = 0; i < t - 1; i++)
            {
                v = v.shiftLeft(1); // v = 1 * 2^(t - 1)
            }
            c = c.modPow(v, p); // c = c^v mod p
            r = r.multiply(c).remainder(p); // r = r * c % p
            c = c.multiply(c).remainder(p); // c = c^2 % p
            n = n.multiply(c).mod(p); // n = n * c % p
        }
        return r;
    }

    /**
     * Computes the greatest common divisor of the two specified integers
     *
     * @param u - first integer
     * @param v - second integer
     * @return gcd(a, b)
     */
    public static int gcd(int u, int v)
    {
        return BigInteger.valueOf(u).gcd(BigInteger.valueOf(v)).intValue();
    }

    /**
     * Extended euclidian algorithm (computes gcd and representation).
     *
     * @param a the first integer
     * @param b the second integer
     * @return <tt>(g,u,v)</tt>, where <tt>g = gcd(abs(a),abs(b)) = ua + vb</tt>
     */
    public static int[] extGCD(int a, int b)
    {
        BigInteger ba = BigInteger.valueOf(a);
        BigInteger bb = BigInteger.valueOf(b);
        BigInteger[] bresult = extgcd(ba, bb);
        int[] result = new int[3];
        result[0] = bresult[0].intValue();
        result[1] = bresult[1].intValue();
        result[2] = bresult[2].intValue();
        return result;
    }

    public static BigInteger divideAndRound(BigInteger a, BigInteger b)
    {
        if (a.signum() < 0)
        {
            return divideAndRound(a.negate(), b).negate();
        }
        if (b.signum() < 0)
        {
            return divideAndRound(a, b.negate()).negate();
        }
        return a.shiftLeft(1).add(b).divide(b.shiftLeft(1));
    }

    public static BigInteger[] divideAndRound(BigInteger[] a, BigInteger b)
    {
        BigInteger[] out = new BigInteger[a.length];
        for (int i = 0; i < a.length; i++)
        {
            out[i] = divideAndRound(a[i], b);
        }
        return out;
    }

    /**
     * Compute the smallest integer that is greater than or equal to the
     * logarithm to the base 2 of the given BigInteger.
     *
     * @param a the integer
     * @return ceil[log(a)]
     */
    public static int ceilLog(BigInteger a)
    {
        int result = 0;
        BigInteger p = ONE;
        while (p.compareTo(a) < 0)
        {
            result++;
            p = p.shiftLeft(1);
        }
        return result;
    }

    /**
     * Compute the smallest integer that is greater than or equal to the
     * logarithm to the base 2 of the given integer.
     *
     * @param a the integer
     * @return ceil[log(a)]
     */
    public static int ceilLog(int a)
    {
        int log = 0;
        int i = 1;
        while (i < a)
        {
            i <<= 1;
            log++;
        }
        return log;
    }

    /**
     * Compute <tt>ceil(log_256 n)</tt>, the number of bytes needed to encode
     * the integer <tt>n</tt>.
     *
     * @param n the integer
     * @return the number of bytes needed to encode <tt>n</tt>
     */
    public static int ceilLog256(int n)
    {
        if (n == 0)
        {
            return 1;
        }
        int m;
        if (n < 0)
        {
            m = -n;
        }
        else
        {
            m = n;
        }

        int d = 0;
        while (m > 0)
        {
            d++;
            m >>>= 8;
        }
        return d;
    }

    /**
     * Compute <tt>ceil(log_256 n)</tt>, the number of bytes needed to encode
     * the long integer <tt>n</tt>.
     *
     * @param n the long integer
     * @return the number of bytes needed to encode <tt>n</tt>
     */
    public static int ceilLog256(long n)
    {
        if (n == 0)
        {
            return 1;
        }
        long m;
        if (n < 0)
        {
            m = -n;
        }
        else
        {
            m = n;
        }

        int d = 0;
        while (m > 0)
        {
            d++;
            m >>>= 8;
        }
        return d;
    }

    /**
     * Compute the integer part of the logarithm to the base 2 of the given
     * integer.
     *
     * @param a the integer
     * @return floor[log(a)]
     */
    public static int floorLog(BigInteger a)
    {
        int result = -1;
        BigInteger p = ONE;
        while (p.compareTo(a) <= 0)
        {
            result++;
            p = p.shiftLeft(1);
        }
        return result;
    }

    /**
     * Compute the integer part of the logarithm to the base 2 of the given
     * integer.
     *
     * @param a the integer
     * @return floor[log(a)]
     */
    public static int floorLog(int a)
    {
        int h = 0;
        if (a <= 0)
        {
            return -1;
        }
        int p = a >>> 1;
        while (p > 0)
        {
            h++;
            p >>>= 1;
        }

        return h;
    }

    /**
     * Compute the largest <tt>h</tt> with <tt>2^h | a</tt> if <tt>a!=0</tt>.
     *
     * @param a an integer
     * @return the largest <tt>h</tt> with <tt>2^h | a</tt> if <tt>a!=0</tt>,
     *         <tt>0</tt> otherwise
     */
    public static int maxPower(int a)
    {
        int h = 0;
        if (a != 0)
        {
            int p = 1;
            while ((a & p) == 0)
            {
                h++;
                p <<= 1;
            }
        }

        return h;
    }

    /**
     * @param a an integer
     * @return the number of ones in the binary representation of an integer
     *         <tt>a</tt>
     */
    public static int bitCount(int a)
    {
        int h = 0;
        while (a != 0)
        {
            h += a & 1;
            a >>>= 1;
        }

        return h;
    }

    /**
     * determines the order of g modulo p, p prime and 1 &lt; g &lt; p. This algorithm
     * is only efficient for small p (see X9.62-1998, p. 68).
     *
     * @param g an integer with 1 &lt; g &lt; p
     * @param p a prime
     * @return the order k of g (that is k is the smallest integer with
     *         g<sup>k</sup> = 1 mod p
     */
    public static int order(int g, int p)
    {
        int b, j;

        b = g % p; // Reduce g mod p first.
        j = 1;

        // Check whether g == 0 mod p (avoiding endless loop).
        if (b == 0)
        {
            throw new IllegalArgumentException(g + " is not an element of Z/("
                + p + "Z)^*; it is not meaningful to compute its order.");
        }

        // Compute the order of g mod p:
        while (b != 1)
        {
            b *= g;
            b %= p;
            if (b < 0)
            {
                b += p;
            }
            j++;
        }

        return j;
    }

    /**
     * Reduces an integer into a given interval
     *
     * @param n     - the integer
     * @param begin - left bound of the interval
     * @param end   - right bound of the interval
     * @return <tt>n</tt> reduced into <tt>[begin,end]</tt>
     */
    public static BigInteger reduceInto(BigInteger n, BigInteger begin,
                                        BigInteger end)
    {
        return n.subtract(begin).mod(end.subtract(begin)).add(begin);
    }

    /**
     * Compute <tt>a<sup>e</sup></tt>.
     *
     * @param a the base
     * @param e the exponent
     * @return <tt>a<sup>e</sup></tt>
     */
    public static int pow(int a, int e)
    {
        int result = 1;
        while (e > 0)
        {
            if ((e & 1) == 1)
            {
                result *= a;
            }
            a *= a;
            e >>>= 1;
        }
        return result;
    }

    /**
     * Compute <tt>a<sup>e</sup></tt>.
     *
     * @param a the base
     * @param e the exponent
     * @return <tt>a<sup>e</sup></tt>
     */
    public static long pow(long a, int e)
    {
        long result = 1;
        while (e > 0)
        {
            if ((e & 1) == 1)
            {
                result *= a;
            }
            a *= a;
            e >>>= 1;
        }
        return result;
    }

    /**
     * Compute <tt>a<sup>e</sup> mod n</tt>.
     *
     * @param a the base
     * @param e the exponent
     * @param n the modulus
     * @return <tt>a<sup>e</sup> mod n</tt>
     */
    public static int modPow(int a, int e, int n)
    {
        if (n <= 0 || (n * n) > Integer.MAX_VALUE || e < 0)
        {
            return 0;
        }
        int result = 1;
        a = (a % n + n) % n;
        while (e > 0)
        {
            if ((e & 1) == 1)
            {
                result = (result * a) % n;
            }
            a = (a * a) % n;
            e >>>= 1;
        }
        return result;
    }

    /**
     * Extended euclidian algorithm (computes gcd and representation).
     *
     * @param a - the first integer
     * @param b - the second integer
     * @return <tt>(d,u,v)</tt>, where <tt>d = gcd(a,b) = ua + vb</tt>
     */
    public static BigInteger[] extgcd(BigInteger a, BigInteger b)
    {
        BigInteger u = ONE;
        BigInteger v = ZERO;
        BigInteger d = a;
        if (b.signum() != 0)
        {
            BigInteger v1 = ZERO;
            BigInteger v3 = b;
            while (v3.signum() != 0)
            {
                BigInteger[] tmp = d.divideAndRemainder(v3);
                BigInteger q = tmp[0];
                BigInteger t3 = tmp[1];
                BigInteger t1 = u.subtract(q.multiply(v1));
                u = v1;
                d = v3;
                v1 = t1;
                v3 = t3;
            }
            v = d.subtract(a.multiply(u)).divide(b);
        }
        return new BigInteger[]{d, u, v};
    }

    /**
     * Computation of the least common multiple of a set of BigIntegers.
     *
     * @param numbers - the set of numbers
     * @return the lcm(numbers)
     */
    public static BigInteger leastCommonMultiple(BigInteger[] numbers)
    {
        int n = numbers.length;
        BigInteger result = numbers[0];
        for (int i = 1; i < n; i++)
        {
            BigInteger gcd = result.gcd(numbers[i]);
            result = result.multiply(numbers[i]).divide(gcd);
        }
        return result;
    }

    /**
     * Returns a long integer whose value is <tt>(a mod m</tt>). This method
     * differs from <tt>%</tt> in that it always returns a <i>non-negative</i>
     * integer.
     *
     * @param a value on which the modulo operation has to be performed.
     * @param m the modulus.
     * @return <tt>a mod m</tt>
     */
    public static long mod(long a, long m)
    {
        long result = a % m;
        if (result < 0)
        {
            result += m;
        }
        return result;
    }

    /**
     * Computes the modular inverse of an integer a
     *
     * @param a   - the integer to invert
     * @param mod - the modulus
     * @return <tt>a<sup>-1</sup> mod n</tt>
     */
    public static int modInverse(int a, int mod)
    {
        return BigInteger.valueOf(a).modInverse(BigInteger.valueOf(mod))
            .intValue();
    }

    /**
     * Computes the modular inverse of an integer a
     *
     * @param a   - the integer to invert
     * @param mod - the modulus
     * @return <tt>a<sup>-1</sup> mod n</tt>
     */
    public static long modInverse(long a, long mod)
    {
        return BigInteger.valueOf(a).modInverse(BigInteger.valueOf(mod))
            .longValue();
    }

    /**
     * Tests whether an integer <tt>a</tt> is power of another integer
     * <tt>p</tt>.
     *
     * @param a - the first integer
     * @param p - the second integer
     * @return n if a = p^n or -1 otherwise
     */
    public static int isPower(int a, int p)
    {
        if (a <= 0)
        {
            return -1;
        }
        int n = 0;
        int d = a;
        while (d > 1)
        {
            if (d % p != 0)
            {
                return -1;
            }
            d /= p;
            n++;
        }
        return n;
    }

    /**
     * Find and return the least non-trivial divisor of an integer <tt>a</tt>.
     *
     * @param a - the integer
     * @return divisor p &gt;1 or 1 if a = -1,0,1
     */
    public static int leastDiv(int a)
    {
        if (a < 0)
        {
            a = -a;
        }
        if (a == 0)
        {
            return 1;
        }
        if ((a & 1) == 0)
        {
            return 2;
        }
        int p = 3;
        while (p <= (a / p))
        {
            if ((a % p) == 0)
            {
                return p;
            }
            p += 2;
        }

        return a;
    }

    /**
     * Miller-Rabin-Test, determines wether the given integer is probably prime
     * or composite. This method returns <tt>true</tt> if the given integer is
     * prime with probability <tt>1 - 2<sup>-20</sup></tt>.
     *
     * @param n the integer to test for primality
     * @return <tt>true</tt> if the given integer is prime with probability
     *         2<sup>-100</sup>, <tt>false</tt> otherwise
     */
    public static boolean isPrime(int n)
    {
        if (n < 2)
        {
            return false;
        }
        if (n == 2)
        {
            return true;
        }
        if ((n & 1) == 0)
        {
            return false;
        }
        if (n < 42)
        {
            for (int i = 0; i < SMALL_PRIMES.length; i++)
            {
                if (n == SMALL_PRIMES[i])
                {
                    return true;
                }
            }
        }

        if ((n % 3 == 0) || (n % 5 == 0) || (n % 7 == 0) || (n % 11 == 0)
            || (n % 13 == 0) || (n % 17 == 0) || (n % 19 == 0)
            || (n % 23 == 0) || (n % 29 == 0) || (n % 31 == 0)
            || (n % 37 == 0) || (n % 41 == 0))
        {
            return false;
        }

        return BigInteger.valueOf(n).isProbablePrime(20);
    }

    /**
     * Short trial-division test to find out whether a number is not prime. This
     * test is usually used before a Miller-Rabin primality test.
     *
     * @param candidate the number to test
     * @return <tt>true</tt> if the number has no factor of the tested primes,
     *         <tt>false</tt> if the number is definitely composite
     */
    public static boolean passesSmallPrimeTest(BigInteger candidate)
    {
        final int[] smallPrime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
            41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103,
            107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
            173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
            239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
            311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
            383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449,
            457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523,
            541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607,
            613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677,
            683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
            769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853,
            857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937,
            941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019,
            1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087,
            1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
            1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229,
            1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297,
            1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381,
            1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453,
            1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499};

        for (int i = 0; i < smallPrime.length; i++)
        {
            if (candidate.mod(BigInteger.valueOf(smallPrime[i])).equals(
                ZERO))
            {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns the largest prime smaller than the given integer
     *
     * @param n - upper bound
     * @return the largest prime smaller than <tt>n</tt>, or <tt>1</tt> if
     *         <tt>n &lt;= 2</tt>
     */
    public static int nextSmallerPrime(int n)
    {
        if (n <= 2)
        {
            return 1;
        }

        if (n == 3)
        {
            return 2;
        }

        if ((n & 1) == 0)
        {
            n--;
        }
        else
        {
            n -= 2;
        }

        while (n > 3 && !isPrime(n))
        {
            n -= 2;
        }
        return n;
    }

    /**
     * Compute the next probable prime greater than <tt>n</tt> with the
     * specified certainty.
     *
     * @param n         a integer number
     * @param certainty the certainty that the generated number is prime
     * @return the next prime greater than <tt>n</tt>
     */
    public static BigInteger nextProbablePrime(BigInteger n, int certainty)
    {

        if (n.signum() < 0 || n.signum() == 0 || n.equals(ONE))
        {
            return TWO;
        }

        BigInteger result = n.add(ONE);

        // Ensure an odd number
        if (!result.testBit(0))
        {
            result = result.add(ONE);
        }

        while (true)
        {
            // Do cheap "pre-test" if applicable
            if (result.bitLength() > 6)
            {
                long r = result.remainder(
                    BigInteger.valueOf(SMALL_PRIME_PRODUCT)).longValue();
                if ((r % 3 == 0) || (r % 5 == 0) || (r % 7 == 0)
                    || (r % 11 == 0) || (r % 13 == 0) || (r % 17 == 0)
                    || (r % 19 == 0) || (r % 23 == 0) || (r % 29 == 0)
                    || (r % 31 == 0) || (r % 37 == 0) || (r % 41 == 0))
                {
                    result = result.add(TWO);
                    continue; // Candidate is composite; try another
                }
            }

            // All candidates of bitLength 2 and 3 are prime by this point
            if (result.bitLength() < 4)
            {
                return result;
            }

            // The expensive test
            if (result.isProbablePrime(certainty))
            {
                return result;
            }

            result = result.add(TWO);
        }
    }

    /**
     * Compute the next probable prime greater than <tt>n</tt> with the default
     * certainty (20).
     *
     * @param n a integer number
     * @return the next prime greater than <tt>n</tt>
     */
    public static BigInteger nextProbablePrime(BigInteger n)
    {
        return nextProbablePrime(n, 20);
    }

    /**
     * Computes the next prime greater than n.
     *
     * @param n a integer number
     * @return the next prime greater than n
     */
    public static BigInteger nextPrime(long n)
    {
        long i;
        boolean found = false;
        long result = 0;

        if (n <= 1)
        {
            return BigInteger.valueOf(2);
        }
        if (n == 2)
        {
            return BigInteger.valueOf(3);
        }

        for (i = n + 1 + (n & 1); (i <= n << 1) && !found; i += 2)
        {
            for (long j = 3; (j <= i >> 1) && !found; j += 2)
            {
                if (i % j == 0)
                {
                    found = true;
                }
            }
            if (found)
            {
                found = false;
            }
            else
            {
                result = i;
                found = true;
            }
        }
        return BigInteger.valueOf(result);
    }

    /**
     * Computes the binomial coefficient (n|t) ("n over t"). Formula:
     * <ul>
     * <li>if n !=0 and t != 0 then (n|t) = Mult(i=1, t): (n-(i-1))/i</li>
     * <li>if t = 0 then (n|t) = 1</li>
     * <li>if n = 0 and t &gt; 0 then (n|t) = 0</li>
     * </ul>
     *
     * @param n - the "upper" integer
     * @param t - the "lower" integer
     * @return the binomialcoefficient "n over t" as BigInteger
     */
    public static BigInteger binomial(int n, int t)
    {

        BigInteger result = ONE;

        if (n == 0)
        {
            if (t == 0)
            {
                return result;
            }
            return ZERO;
        }

        // the property (n|t) = (n|n-t) be used to reduce numbers of operations
        if (t > (n >>> 1))
        {
            t = n - t;
        }

        for (int i = 1; i <= t; i++)
        {
            result = (result.multiply(BigInteger.valueOf(n - (i - 1))))
                .divide(BigInteger.valueOf(i));
        }

        return result;
    }

    public static BigInteger randomize(BigInteger upperBound)
    {
        if (sr == null)
        {
            sr = CryptoServicesRegistrar.getSecureRandom();
        }
        return randomize(upperBound, sr);
    }

    public static BigInteger randomize(BigInteger upperBound,
                                       SecureRandom prng)
    {
        int blen = upperBound.bitLength();
        BigInteger randomNum = BigInteger.valueOf(0);

        if (prng == null)
        {
            prng = sr != null ? sr : CryptoServicesRegistrar.getSecureRandom();
        }

        for (int i = 0; i < 20; i++)
        {
            randomNum = BigIntegers.createRandomBigInteger(blen, prng);
            if (randomNum.compareTo(upperBound) < 0)
            {
                return randomNum;
            }
        }
        return randomNum.mod(upperBound);
    }

    /**
     * Extract the truncated square root of a BigInteger.
     *
     * @param a - value out of which we extract the square root
     * @return the truncated square root of <tt>a</tt>
     */
    public static BigInteger squareRoot(BigInteger a)
    {
        int bl;
        BigInteger result, remainder, b;

        if (a.compareTo(ZERO) < 0)
        {
            throw new ArithmeticException(
                "cannot extract root of negative number" + a + ".");
        }

        bl = a.bitLength();
        result = ZERO;
        remainder = ZERO;

        // if the bit length is odd then extra step
        if ((bl & 1) != 0)
        {
            result = result.add(ONE);
            bl--;
        }

        while (bl > 0)
        {
            remainder = remainder.multiply(FOUR);
            remainder = remainder.add(BigInteger.valueOf((a.testBit(--bl) ? 2
                : 0)
                + (a.testBit(--bl) ? 1 : 0)));
            b = result.multiply(FOUR).add(ONE);
            result = result.multiply(TWO);
            if (remainder.compareTo(b) != -1)
            {
                result = result.add(ONE);
                remainder = remainder.subtract(b);
            }
        }

        return result;
    }

    /**
     * Takes an approximation of the root from an integer base, using newton's
     * algorithm
     *
     * @param base the base to take the root from
     * @param root the root, for example 2 for a square root
     */
    public static float intRoot(int base, int root)
    {
        float gNew = base / root;
        float gOld = 0;
        int counter = 0;
        while (Math.abs(gOld - gNew) > 0.0001)
        {
            float gPow = floatPow(gNew, root);
            while (Float.isInfinite(gPow))
            {
                gNew = (gNew + gOld) / 2;
                gPow = floatPow(gNew, root);
            }
            counter += 1;
            gOld = gNew;
            gNew = gOld - (gPow - base) / (root * floatPow(gOld, root - 1));
        }
        return gNew;
    }

    /**
     * int power of a base float, only use for small ints
     *
     * @param f base float
     * @param i power to be raised to.
     * @return int power i of f
     */
    public static float floatPow(float f, int i)
    {
        float g = 1;
        for (; i > 0; i--)
        {
            g *= f;
        }
        return g;
    }

    public static boolean isIncreasing(int[] a)
    {
        for (int i = 1; i < a.length; i++)
        {
            if (a[i - 1] >= a[i])
            {
                System.out.println("a[" + (i - 1) + "] = " + a[i - 1] + " >= "
                    + a[i] + " = a[" + i + "]");
                return false;
            }
        }
        return true;
    }

    public static byte[] integerToOctets(BigInteger val)
    {
        byte[] valBytes = val.abs().toByteArray();

        // check whether the array includes a sign bit
        if ((val.bitLength() & 7) != 0)
        {
            return valBytes;
        }
        // get rid of the sign bit (first byte)
        byte[] tmp = new byte[val.bitLength() >> 3];
        System.arraycopy(valBytes, 1, tmp, 0, tmp.length);
        return tmp;
    }

    public static BigInteger octetsToInteger(byte[] data, int offset,
                                             int length)
    {
        byte[] val = new byte[length + 1];

        val[0] = 0;
        System.arraycopy(data, offset, val, 1, length);
        return new BigInteger(val);
    }

    public static BigInteger octetsToInteger(byte[] data)
    {
        return octetsToInteger(data, 0, data.length);
    }
}
