package string;

import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

public class StringAlgorithmsTest {

    @Test
    public void testKmpSearch() {
        List<Integer> res = StringAlgorithms.kmpSearch("abababc", "ababc");
        assertEquals(Arrays.asList(2), res);
    }

    @Test
    public void testKmpSearchMultiple() {
        List<Integer> res = StringAlgorithms.kmpSearch("aaaa", "aa");
        assertEquals(Arrays.asList(0, 1, 2), res);
    }

    @Test
    public void testZFunction() {
        int[] z = StringAlgorithms.zFunction("aaaaa");
        assertArrayEquals(new int[]{0, 4, 3, 2, 1}, z);
    }

    @Test
    public void testManacher() {
        int[] p = StringAlgorithms.manacher("abba");
        int maxR = Arrays.stream(p).max().orElse(0);
        assertTrue(maxR >= 4);
    }

    @Test
    public void testRollingHash() {
        StringAlgorithms.RollingHash rh = new StringAlgorithms.RollingHash("hello world", 911, 1_000_000_007L);
        assertEquals(rh.getHash(0, 5), rh.getHash(0, 5));
    }
}
