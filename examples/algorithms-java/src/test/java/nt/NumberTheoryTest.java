package nt;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class NumberTheoryTest {

    @Test
    public void testGcd() {
        assertEquals(6, NumberTheory.gcd(48, 18));
        assertEquals(1, NumberTheory.gcd(101, 103));
    }

    @Test
    public void testLcm() {
        assertEquals(12, NumberTheory.lcm(4, 6));
    }

    @Test
    public void testExtendedGcd() {
        long[] res = NumberTheory.extendedGcd(30, 12);
        assertEquals(6, res[0]);
        assertEquals(30 * res[1] + 12 * res[2], res[0]);
    }

    @Test
    public void testModInverse() {
        assertEquals(Long.valueOf(4), NumberTheory.modInverse(3, 11));
    }

    @Test
    public void testFastPow() {
        assertEquals(24, NumberTheory.fastPow(2, 10, 1000));
    }

    @Test
    public void testIsPrime() {
        assertTrue(NumberTheory.isPrime(97, 5));
        assertFalse(NumberTheory.isPrime(100, 5));
    }

    @Test
    public void testSieve() {
        boolean[] sp = NumberTheory.sieve(10);
        assertTrue(sp[2] && sp[3] && sp[5] && sp[7]);
        assertFalse(sp[4] || sp[9]);
    }
}
