package leibniz.internal;

/**
 * Created by alex on 10/29/17.
 */
public class JavaEq {
    public static boolean equal(Double x, Double y) {
        if (x == null) return y == null;
        return Double.doubleToRawLongBits(x) == Double.doubleToRawLongBits(y);
    }
}
