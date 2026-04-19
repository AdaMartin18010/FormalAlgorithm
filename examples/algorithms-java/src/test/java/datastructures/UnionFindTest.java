package datastructures;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class UnionFindTest {

    @Test
    public void testBasic() {
        UnionFind uf = new UnionFind(5);
        assertEquals(5, uf.count());
        uf.union(0, 1);
        assertTrue(uf.connected(0, 1));
        assertEquals(4, uf.count());
        uf.union(1, 2);
        assertTrue(uf.connected(0, 2));
        assertEquals(3, uf.count());
    }

    @Test
    public void testNoConnection() {
        UnionFind uf = new UnionFind(5);
        uf.union(0, 1);
        uf.union(2, 3);
        assertFalse(uf.connected(0, 2));
        assertEquals(3, uf.count());
    }

    @Test
    public void testSelfConnection() {
        UnionFind uf = new UnionFind(3);
        assertTrue(uf.connected(0, 0));
    }

    @Test
    public void testLarge() {
        int n = 1000;
        UnionFind uf = new UnionFind(n);
        for (int i = 0; i < n - 1; i++) {
            uf.union(i, i + 1);
        }
        assertEquals(1, uf.count());
        assertTrue(uf.connected(0, n - 1));
    }

    @Test
    public void testPathCompression() {
        UnionFind uf = new UnionFind(5);
        uf.union(0, 1);
        uf.union(1, 2);
        uf.union(2, 3);
        uf.union(3, 4);
        int root = uf.find(0);
        for (int i = 1; i < 5; i++) {
            assertEquals(root, uf.find(i));
        }
    }
}
