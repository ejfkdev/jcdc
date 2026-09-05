package feat;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ControlFlow {
    static int counter = 0;

    public static void main(String[] args) {
        System.out.println("ifElse=" + ifElse(5) + "," + ifElse(-5) + "," + ifElse(0));
        System.out.println("chain=" + chain(1) + chain(5) + chain(50) + chain(500));
        System.out.println("loops=" + whileLoop(10) + "," + doWhile(0) + "," + doWhile(3) + "," + forLoop(5));
        System.out.println("foreach=" + forEach() + "," + forEachArr());
        System.out.println("switch=" + switchInt(2) + switchInt(99) + "|" + switchStr("apple") + switchStr("banana") + switchStr("xx"));
        System.out.println("nested=" + nestedLoops(3));
        System.out.println("labels=" + labeled());
        System.out.println("ternary=" + ternary(true) + ternary(false));
        System.out.println("bool=" + boolOps(true, false) + andOr(false) + orShort(true));
        System.out.println("cmp=" + compareChain(7));
        System.out.println("empty=" + emptyLoop());
        System.out.println("breakIf=" + breakInLoop(4));
        System.out.println("contIf=" + continueInLoop(10));
        System.out.println("diamond=" + diamond(3));
        System.out.println("switchFall=" + switchFall(2));
        System.out.println("counter=" + counter);
    }

    static String ifElse(int x) {
        if (x > 0) {
            return "pos";
        } else if (x < 0) {
            return "neg";
        } else {
            return "zero";
        }
    }

    static int chain(int x) {
        if (x > 100) return 1;
        if (x > 10) return 2;
        if (x > 0) return 3;
        return 4;
    }

    static int whileLoop(int n) {
        int sum = 0;
        int i = 0;
        while (i < n) {
            sum += i;
            i++;
        }
        return sum;
    }

    static int doWhile(int n) {
        int count = 0;
        do {
            count++;
            n = n - 1;
        } while (n > 0);
        return count;
    }

    static int forLoop(int n) {
        int prod = 1;
        for (int i = 1; i <= n; i++) {
            prod *= i;
        }
        return prod;
    }

    static int forEach() {
        List<Integer> list = new ArrayList<>();
        list.add(1); list.add(2); list.add(3);
        int sum = 0;
        for (Integer i : list) {
            sum += i;
        }
        return sum;
    }

    static int forEachArr() {
        int[] arr = {4, 5, 6};
        int sum = 0;
        for (int i : arr) sum += i;
        return sum;
    }

    static String switchInt(int x) {
        switch (x) {
            case 1: return "one";
            case 2: return "two";
            case 3:
            case 4: return "threefour";
            default: return "other";
        }
    }

    static String switchStr(String s) {
        switch (s) {
            case "apple": return "A";
            case "banana": return "B";
            default: return "?";
        }
    }

    static int switchFall(int x) {
        int r = 0;
        switch (x) {
            case 1: r += 1;
            case 2: r += 2;
            case 3: r += 4; break;
            case 4: r += 8;
            default: r += 100;
        }
        return r;
    }

    static int nestedLoops(int n) {
        int c = 0;
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (i == j) continue;
                c++;
            }
        }
        return c;
    }

    static String labeled() {
        outer:
        for (int i = 0; i < 5; i++) {
            for (int j = 0; j < 5; j++) {
                if (j == 3) continue outer;
                if (i == 3) break outer;
                counter++;
            }
        }
        return "c" + counter;
    }

    static int ternary(boolean b) {
        return b ? 1 : 2;
    }

    static String boolOps(boolean a, boolean b) {
        return (a && b) + "|" + (a || b) + "|" + (!a);
    }

    static boolean andOr(boolean x) {
        return x && !x || true && (false || x);
    }

    static int orShort(boolean t) {
        if (t || explode()) return 1;
        return 2;
    }

    static boolean explode() {
        throw new RuntimeException("short circuit failed");
    }

    static String compareChain(int x) {
        if (x >= 5 && x <= 10) return "in";
        if (x < 0 || x > 100) return "out";
        return "mid";
    }

    static int emptyLoop() {
        int i = 0;
        while (i < 100) i++;
        return i;
    }

    static int breakInLoop(int target) {
        for (int i = 0; ; i++) {
            if (i == target) return i;
        }
    }

    static int continueInLoop(int n) {
        int sum = 0;
        for (int i = 0; i < n; i++) {
            if (i % 2 == 0) continue;
            sum += i;
        }
        return sum;
    }

    static int diamond(int x) {
        int a;
        if (x > 0) {
            a = x * 2;
        } else {
            a = x * 3;
        }
        return a + 1;
    }
}
