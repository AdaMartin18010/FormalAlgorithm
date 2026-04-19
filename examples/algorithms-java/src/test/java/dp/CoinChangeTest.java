package dp;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class CoinChangeTest {

    @Test
    public void testMinCoins() {
        assertEquals(3, CoinChange.minCoins(new int[]{1, 2, 5}, 11));
        assertEquals(2, CoinChange.minCoins(new int[]{1, 2, 5}, 3));
        assertEquals(-1, CoinChange.minCoins(new int[]{2}, 3));
        assertEquals(0, CoinChange.minCoins(new int[]{1}, 0));
        assertEquals(2, CoinChange.minCoins(new int[]{1, 3, 4}, 6));
    }

    @Test
    public void testWays() {
        assertEquals(4, CoinChange.ways(new int[]{1, 2, 5}, 5));
        assertEquals(0, CoinChange.ways(new int[]{2}, 3));
        assertEquals(6, CoinChange.ways(new int[]{1, 3, 4}, 6));
        assertEquals(4, CoinChange.ways(new int[]{1, 2, 3}, 4));
    }
}
