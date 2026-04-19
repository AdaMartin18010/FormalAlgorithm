import search.BinarySearch;
import graph.BFS;
import graph.DFS;
import datastructures.UnionFind;
import dp.LIS;
import dp.CoinChange;
import java.util.*;

/**
 * Simple test runner for validation without JUnit/Maven.
 */
public class TestRunner {
    static int passed = 0;
    static int failed = 0;

    static void assertEq(String name, int expected, int actual) {
        if (expected == actual) {
            passed++;
        } else {
            failed++;
            System.out.println("FAIL " + name + ": expected " + expected + ", got " + actual);
        }
    }

    static void assertTrue(String name, boolean condition) {
        if (condition) {
            passed++;
        } else {
            failed++;
            System.out.println("FAIL " + name);
        }
    }

    public static void main(String[] args) {
        // BinarySearch tests
        int[] arr = {1, 3, 5, 7, 9};
        assertEq("BS found", 2, BinarySearch.search(arr, 5));
        assertEq("BS not found", -1, BinarySearch.search(arr, 4));
        assertEq("BS empty", -1, BinarySearch.search(new int[]{}, 1));
        assertEq("LowerBound", 2, BinarySearch.lowerBound(arr, 5));
        assertEq("UpperBound", 4, BinarySearch.upperBound(new int[]{1,3,5,5,7,9}, 5));

        // BFS tests
        Map<Integer, List<Integer>> graph = new HashMap<>();
        graph.put(0, Arrays.asList(1, 2));
        graph.put(1, Arrays.asList(2));
        graph.put(2, Arrays.asList(3));
        graph.put(3, Collections.emptyList());
        assertTrue("BFS order", BFS.traverse(graph, 0).equals(Arrays.asList(0, 1, 2, 3)));
        assertTrue("BFS path", BFS.shortestPath(graph, 0, 3).size() == 3);

        // DFS tests
        assertTrue("DFS size", DFS.traverse(graph, 0).size() == 4);
        assertTrue("HasPath", DFS.hasPath(graph, 0, 3));
        assertTrue("NoPath", !DFS.hasPath(graph, 2, 0));

        // UnionFind tests
        UnionFind uf = new UnionFind(5);
        uf.union(0, 1);
        assertTrue("UF connected", uf.connected(0, 1));
        assertEq("UF count", 4, uf.count());
        uf.union(1, 2);
        assertTrue("UF transitive", uf.connected(0, 2));

        // LIS tests
        assertEq("LIS length", 4, LIS.length(new int[]{10, 9, 2, 5, 3, 7, 101, 18}));
        assertTrue("LIS sequence", LIS.sequence(new int[]{10, 9, 2, 5, 3, 7, 101, 18}).size() == 4);

        // CoinChange tests
        assertEq("CC min", 3, CoinChange.minCoins(new int[]{1, 2, 5}, 11));
        assertEq("CC ways", 4, CoinChange.ways(new int[]{1, 2, 5}, 5));
        assertEq("CC impossible", -1, CoinChange.minCoins(new int[]{2}, 3));

        System.out.println("\n=== Results ===");
        System.out.println("Passed: " + passed);
        System.out.println("Failed: " + failed);
        System.exit(failed > 0 ? 1 : 0);
    }
}
