package search;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class BinarySearchTest {

    @Test
    public void testBasic() {
        int[] arr = {1, 3, 5, 7, 9};
        assertEquals(2, BinarySearch.search(arr, 5));
        assertEquals(0, BinarySearch.search(arr, 1));
        assertEquals(4, BinarySearch.search(arr, 9));
    }

    @Test
    public void testNotFound() {
        int[] arr = {1, 3, 5, 7, 9};
        assertEquals(-1, BinarySearch.search(arr, 0));
        assertEquals(-1, BinarySearch.search(arr, 10));
        assertEquals(-1, BinarySearch.search(arr, 4));
    }

    @Test
    public void testEmpty() {
        assertEquals(-1, BinarySearch.search(new int[]{}, 1));
    }

    @Test
    public void testSingleElement() {
        assertEquals(0, BinarySearch.search(new int[]{5}, 5));
        assertEquals(-1, BinarySearch.search(new int[]{5}, 3));
    }

    @Test
    public void testLowerBound() {
        int[] arr = {1, 3, 5, 5, 7, 9};
        assertEquals(2, BinarySearch.lowerBound(arr, 5));
        assertEquals(2, BinarySearch.lowerBound(arr, 4));
        assertEquals(6, BinarySearch.lowerBound(arr, 10));
    }

    @Test
    public void testUpperBound() {
        int[] arr = {1, 3, 5, 5, 7, 9};
        assertEquals(4, BinarySearch.upperBound(arr, 5));
        assertEquals(2, BinarySearch.upperBound(arr, 4));
        assertEquals(6, BinarySearch.upperBound(arr, 10));
    }
}
