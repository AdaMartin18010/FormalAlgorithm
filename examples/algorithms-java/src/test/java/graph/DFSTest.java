package graph;

import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

public class DFSTest {

    @Test
    public void testBasic() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1, 2));
        graph.put(1, Arrays.asList(3));
        graph.put(2, Arrays.asList(3));
        graph.put(3, Collections.emptyList());
        List<Integer> result = DFS.traverse(graph, 0);
        assertEquals(4, result.size());
        assertEquals(Integer.valueOf(0), result.get(0));
        Set<Integer> seen = new HashSet<>(result);
        assertEquals(Set.of(0, 1, 2, 3), seen);
    }

    @Test
    public void testSingleVertex() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Collections.emptyList());
        assertEquals(Arrays.asList(0), DFS.traverse(graph, 0));
    }

    @Test
    public void testEmptyGraph() {
        assertTrue(DFS.traverse(new HashMap<>(), 0).isEmpty());
    }

    @Test
    public void testHasPath() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1, 2));
        graph.put(1, Arrays.asList(3));
        graph.put(2, Collections.emptyList());
        graph.put(3, Collections.emptyList());
        assertTrue(DFS.hasPath(graph, 0, 3));
        assertFalse(DFS.hasPath(graph, 2, 3));
        assertTrue(DFS.hasPath(graph, 0, 0));
    }
}
