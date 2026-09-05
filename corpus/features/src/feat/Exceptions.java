package feat;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

public class Exceptions {
    public static void main(String[] args) throws Exception {
        System.out.println("basic=" + basic());
        System.out.println("multi=" + multi(1) + multi(2) + multi(3));
        System.out.println("finallyFlow=" + finallyBasic());
        System.out.println("finallyRet=" + finallyReturn());
        System.out.println("finallyThrow=" + finallyThrow());
        System.out.println("nested=" + nestedTry());
        System.out.println("twr=" + tryWithResources());
        System.out.println("twr2=" + tryWithResources2());
        System.out.println("catchRethrow=" + catchRethrow());
        System.out.println("loopTry=" + loopTry());
    }

    static String basic() {
        try {
            throw new IllegalStateException("x");
        } catch (IllegalStateException e) {
            return "caught:" + e.getMessage();
        }
    }

    static String multi(int which) {
        try {
            if (which == 1) throw new IllegalArgumentException("a");
            if (which == 2) throw new IndexOutOfBoundsException("b");
            if (which == 3) throw new RuntimeException("c");
        } catch (IllegalArgumentException | IndexOutOfBoundsException e) {
            return "multi:" + e.getMessage();
        } catch (RuntimeException e) {
            return "rt:" + e.getMessage();
        } finally {
            System.out.print("[f]");
        }
        return "none";
    }

    static int finallyBasic() {
        int x = 1;
        try {
            x = 2;
        } finally {
            x = x + 10;
        }
        return x;
    }

    static int finallyReturn() {
        try {
            return 1;
        } finally {
            System.out.print("[fr]");
        }
    }

    static String finallyThrow() {
        try {
            try {
                if (System.nanoTime() >= 0) throw new RuntimeException("inner");
            } finally {
                System.out.print("[ft]");
            }
        } catch (RuntimeException e) {
            return "ok:" + e.getMessage();
        }
        return "?";
    }

    static String nestedTry() {
        StringBuilder sb = new StringBuilder();
        try {
            sb.append("a");
            try {
                sb.append("b");
                throw new Exception("deep");
            } catch (Exception e) {
                sb.append("c:").append(e.getMessage());
            } finally {
                sb.append("d");
            }
            sb.append("e");
        } catch (RuntimeException re) {
            sb.append("f");
        } finally {
            sb.append("g");
        }
        return sb.toString();
    }

    static String tryWithResources() throws IOException {
        StringBuilder out = new StringBuilder();
        try (StringReader sr = new StringReader("hello")) {
            BufferedReader br = new BufferedReader(sr);
            out.append(br.readLine());
        }
        return out.toString();
    }

    static String tryWithResources2() throws IOException {
        try (StringReader a = new StringReader("x");
             StringReader b = new StringReader("y")) {
            return "" + (char) a.read() + (char) b.read();
        }
    }

    static String catchRethrow() {
        try {
            try {
                throw new RuntimeException("1");
            } catch (RuntimeException e) {
                throw new RuntimeException("2:" + e.getMessage(), e);
            }
        } catch (RuntimeException e) {
            return e.getMessage();
        }
    }

    static int loopTry() {
        int sum = 0;
        for (int i = 0; i < 5; i++) {
            try {
                if (i == 2) throw new Exception("skip");
                sum += i;
            } catch (Exception e) {
                sum += 100;
            } finally {
                sum += 1;
            }
        }
        return sum;
    }
}
