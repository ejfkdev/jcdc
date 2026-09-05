package feat;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Java 6-era feature coverage: generics, varargs, enums with bodies,
 * anonymous/inner classes, boxing, StringBuffer concat, synchronized,
 * try/finally. No diamond, no lambdas, no TWR, no string switch.
 */
public class Legacy6 {
    static int counter = 0;
    final int base;

    public Legacy6(int base) {
        this.base = base;
    }

    public static void main(String[] args) {
        System.out.println("loops=" + loops(4));
        System.out.println("box=" + boxing(3));
        System.out.println("varargs=" + sum(1, 2, 3));
        System.out.println("foreach=" + each());
        System.out.println("enum=" + Suit.HEARTS.rank() + Suit.SPADES.rank());
        System.out.println("anon=" + anon(5));
        System.out.println("inner=" + new Legacy6(7).inner().get());
        System.out.println("strbuf=" + buf(2));
        System.out.println("nested=" + nested(3, 4));
        System.out.println("fin=" + fin(false));
        System.out.println("sync=" + sync());
        System.out.println("gen=" + generics());
        System.out.println("cmp=" + compare(2, 5));
    }

    static int loops(int n) {
        int s = 0;
        for (int i = 0; i < n; i++) {
            s += i;
            if (i == 2) {
                continue;
            }
        }
        int j = n;
        do {
            j--;
        } while (j > 0);
        outer:
        for (int a = 0; a < 3; a++) {
            for (int b = 0; b < 3; b++) {
                if (a == 2 && b == 2) {
                    break outer;
                }
                counter++;
            }
        }
        return s + j + counter;
    }

    static String boxing(int x) {
        Integer boxed = Integer.valueOf(x);
        List<Integer> list = new ArrayList<Integer>();
        list.add(boxed);
        list.add(Integer.valueOf(x * 2));
        int un = ((Integer) list.get(0)).intValue();
        return un + "," + list.size();
    }

    static int sum(int... vals) {
        int t = 0;
        for (int i = 0; i < vals.length; i++) {
            t += vals[i];
        }
        return t;
    }

    static int each() {
        List<Integer> list = new ArrayList<Integer>();
        list.add(Integer.valueOf(1));
        list.add(Integer.valueOf(2));
        list.add(Integer.valueOf(3));
        int s = 0;
        for (Iterator<Integer> it = list.iterator(); it.hasNext();) {
            s += ((Integer) it.next()).intValue();
        }
        int[] arr = {4, 5, 6};
        for (int i = 0; i < arr.length; i++) {
            s += arr[i];
        }
        return s;
    }

    enum Suit {
        HEARTS(1), SPADES(4);
        private final int v;

        Suit(int v) {
            this.v = v;
        }

        int rank() {
            return v * 10;
        }
    }

    interface Fn {
        int apply(int x);
    }

    static int anon(final int n) {
        Fn f = new Fn() {
            public int apply(int x) {
                return x * n;
            }
        };
        return f.apply(3);
    }

    class Inner {
        int get() {
            return base * 2;
        }
    }

    Inner inner() {
        return new Inner();
    }

    static String buf(int x) {
        StringBuffer sb = new StringBuffer();
        sb.append("v=");
        sb.append(x);
        sb.append(";");
        return sb.toString() + "tail" + (x + 1);
    }

    static int nested(int a, int b) {
        int m = a > b ? a : b;
        int n = a < b ? a : (a == b ? 0 : -1);
        return m * 100 + n;
    }

    static String fin(boolean fail) {
        StringBuffer t = new StringBuffer();
        try {
            t.append("try");
            if (fail) {
                throw new IllegalStateException("x");
            }
        } catch (IllegalStateException e) {
            t.append("catch");
        } finally {
            t.append("fin");
        }
        return t.toString();
    }

    static synchronized int sync() {
        Object lock = new Object();
        synchronized (lock) {
            counter += 3;
        }
        return counter;
    }

    static String generics() {
        List<String> names = new ArrayList<String>();
        names.add("a");
        names.add("b");
        StringBuilder joined = new StringBuilder();
        for (String s : names) {
            joined.append(s);
        }
        return joined.toString();
    }

    static String compare(int a, int b) {
        if (a < b) {
            return "lt";
        } else if (a == b) {
            return "eq";
        }
        return "gt";
    }
}
