package geometry;

import org.junit.jupiter.api.Test;
import java.util.*;
import static org.junit.jupiter.api.Assertions.*;

public class GeometryTest {

    @Test
    public void testConvexHull() {
        List<Geometry.Point> pts = Arrays.asList(
            new Geometry.Point(0, 0),
            new Geometry.Point(1, 1),
            new Geometry.Point(1, 0),
            new Geometry.Point(0, 1),
            new Geometry.Point(0.5, 0.5)
        );
        List<Geometry.Point> hull = Geometry.convexHull(pts);
        assertEquals(4, hull.size());
    }

    @Test
    public void testSegmentsIntersect() {
        assertTrue(Geometry.segmentsIntersect(
            new Geometry.Point(0, 0), new Geometry.Point(10, 10),
            new Geometry.Point(0, 10), new Geometry.Point(10, 0)
        ));
        assertFalse(Geometry.segmentsIntersect(
            new Geometry.Point(0, 0), new Geometry.Point(5, 5),
            new Geometry.Point(6, 6), new Geometry.Point(10, 10)
        ));
    }
}
