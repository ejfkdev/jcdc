package feat;

public class EnumSwitch {
    public enum Color {
        RED, GREEN("g"), BLUE;
        private final String tag;

        Color() {
            this("default");
        }

        Color(String tag) {
            this.tag = tag;
        }

        String tag() {
            return tag;
        }

        boolean warm() {
            return this == RED;
        }
    }

    public enum Operation {
        PLUS {
            int apply(int a, int b) { return a + b; }
        },
        MINUS {
            int apply(int a, int b) { return a - b; }
        };
        abstract int apply(int a, int b);
    }

    enum Private { A, B }

    public static void main(String[] args) {
        System.out.println("switch=" + describe(Color.RED) + describe(Color.GREEN) + describe(Color.BLUE));
        System.out.println("values=" + java.util.Arrays.toString(Color.values()));
        System.out.println("valueOf=" + Color.valueOf("BLUE"));
        System.out.println("ordinal=" + Color.GREEN.ordinal() + "," + Color.RED.name());
        System.out.println("warm=" + Color.RED.warm() + Color.BLUE.warm());
        System.out.println("op=" + Operation.PLUS.apply(2, 3) + Operation.MINUS.apply(9, 4));
        System.out.println("inLoop=" + loopColors());
        System.out.println("private=" + Private.A.ordinal());
        System.out.println("nestedEnum=" + Outer.InnerEnum.X.name());
    }

    static String describe(Color c) {
        switch (c) {
            case RED: return "R";
            case GREEN: return "G:" + c.tag();
            case BLUE: return "B";
            default: throw new IllegalStateException();
        }
    }

    static String loopColors() {
        StringBuilder sb = new StringBuilder();
        for (Color c : Color.values()) {
            switch (c) {
                case RED:
                case BLUE: sb.append('x'); break;
                default: sb.append(c.tag());
            }
        }
        return sb.toString();
    }

    static class Outer {
        enum InnerEnum { X, Y }
    }
}
