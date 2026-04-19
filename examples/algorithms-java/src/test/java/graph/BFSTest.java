package graph;

import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

public class BFSTest {

    @Test
    public void testBasic() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1, 2));
        graph.put(1, Arrays.asList(2));
        graph.put(2, Arrays.asList(3));
        graph.put(3, Collections.emptyList());
        assertEquals(Arrays.asList(0, 1, 2, 3), BFS.traverse(graph, 0));
    }

    @Test
    public void testSingleVertex() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Collections.emptyList());
        assertEquals(Arrays.asList(0), BFS.traverse(graph, 0));
    }

    @Test
    public void testEmptyGraph() {
        assertTrue(BFS.traverse(new HashMap<>(), 0).isEmpty());
    }

    @Test
    public void testShortestPath() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1, 2));
        graph.put(1, Arrays.asList(3));
        graph.put(2, Arrays.asList(3));
        graph.put(3, Collections.emptyList());
        List<Integer> path = BFS.shortestPath(graph, 0, 3);
        assertNotNull(path);
        assertEquals(3, path.size());
        assertEquals(Integer.valueOf(0), path.get(0));
        assertEquals(Integer.valueOf(3), path.get(2));
    }

    @Test
    public void testNoPath() {
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1));
        graph.put(1, Collections.emptyList());
        graph.put(2, Arrays.asList(3));
        graph.put(3, Collections.emptyList());
        assertNull(BFS.shortestPath(graph, 0, 3));
    }
}
