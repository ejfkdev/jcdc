package feat;

import java.util.List;

public class Modern {
    public record Point(int x, int y) {
        public record Nested(String s) {}

        double norm() {
            return Math.sqrt((double) x * x + (double) y * y);
        }

        public static Point origin() {
            return new Point(0, 0);
        }
    }

    public record Empty() {}

    public record Generic<T>(T value, List<T> others) {}

    public sealed interface Shape permits Circle, Square, Rect {}

    public static final class Circle implements Shape {
        final double r;
        Circle(double r) { this.r = r; }
    }

    public static non-sealed class Square implements Shape {
        final double s;
        Square(double s) { this.s = s; }
    }

    public sealed static class Rect implements Shape permits Tall {
        final double w;
        final double h;
        Rect(double w, double h) { this.w = w; this.h = h; }
    }

    public static final class Tall extends Rect {
        Tall() { super(1, 2); }
    }

    public static void main(String[] args) {
        var list = new java.util.ArrayList<String>();
        list.add("v");
        System.out.println("var=" + list);
        Point p = new Point(3, 4);
        System.out.println("record=" + p + "," + p.x() + "," + p.norm() + "," + p.equals(new Point(3, 4)) + "," + Point.origin());
        System.out.println("empty=" + new Empty());
        System.out.println("generic=" + new Generic<>("s", List.of("a")));
        System.out.println("sealed=" + describe(new Circle(1)) + describe(new Square(2)) + describe(new Tall()));
        System.out.println("nestedRecord=" + new Point.Nested("n"));
    }

    static String describe(Shape s) {
        if (s instanceof Circle) {
            return "circle";
        }
        if (s instanceof Square) {
            return "square";
        }
        return "rect";
    }
}
