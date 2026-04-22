package tree;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class TreeAlgorithmsTest {

    @Test
    public void testLCA() {
        int[][] adj = {{1, 2}, {3, 4}, {5}, {}, {}, {}};
        TreeAlgorithms.LCA lca = new TreeAlgorithms.LCA(adj, 0);
        assertEquals(1, lca.query(3, 4));
        assertEquals(0, lca.query(3, 5));
        assertEquals(0, lca.query(1, 2));
    }

    @Test
    public void testCartesianTree() {
        int[] arr = {3, 2, 6, 1, 0, 8, 7};
        TreeAlgorithms.CartesianTree ct = new TreeAlgorithms.CartesianTree(arr);
        assertEquals(4, ct.root);
    }
}
