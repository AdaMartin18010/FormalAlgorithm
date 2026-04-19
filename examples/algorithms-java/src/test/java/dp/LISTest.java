package dp;

import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

public class LISTest {

    @Test
    public void testLength() {
        assertEquals(4, LIS.length(new int[]{10, 9, 2, 5, 3, 7, 101, 18}));
        assertEquals(0, LIS.length(new int[]{}));
        assertEquals(1, LIS.length(new int[]{1}));
        assertEquals(5, LIS.length(new int[]{1, 2, 3, 4, 5}));
        assertEquals(1, LIS.length(new int[]{5, 4, 3, 2, 1}));
    }

    @Test
    public void testSequence() {
        List<Integer> result = LIS.sequence(new int[]{10, 9, 2, 5, 3, 7, 101, 18});
        assertEquals(4, result.size());
        for (int i = 1; i < result.size(); i++) {
            assertTrue(result.get(i) > result.get(i - 1));
        }
    }

    @Test
    public void testSequenceEmpty() {
        assertTrue(LIS.sequence(new int[]{}).isEmpty());
    }
}
