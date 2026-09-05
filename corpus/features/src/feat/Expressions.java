package feat;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;

public class Expressions {
    static final int CONST = 42;
    static final String S = "str";
    static final long L = 1234567890123L;
    static final double D = 3.14159;
    static final float F = 2.5f;
    static final boolean B = true;
    static final char C = 'x';
    static final byte BY = 7;
    static final short SH = 300;

    public static void main(String[] args) {
        System.out.println("arith=" + (3 + 4 * 2 - 6 / 3 % 4));
        System.out.println("wide=" + (L * 2 + (long) CONST));
        System.out.println("floats=" + (D * F) + "," + (1.0 / 3.0));
        System.out.println("bits=" + (0xFF & 0x0F) + "," + (1 << 10) + "," + (-16 >> 2) + "," + (-16 >>> 28));
        System.out.println("longbits=" + ((1L << 40) ^ 0xFL) + "," + (L & 0xFFL));
        System.out.println("neg=" + (-CONST) + "," + (-D));
        System.out.println("cmp=" + (3 < 4) + (3.0 == 3.0) + (Long.compare(L, 0L)));
        System.out.println("cast=" + ((int) D) + "," + ((byte) 300) + "," + ((char) 65) + "," + (short) (BY + SH));
        System.out.println("str=" + ("a" + 1 + true + 'c' + null + S));
        System.out.println("strfmt=" + String.format("%s=%d", S, CONST));
        System.out.println("concatMany=" + (CONST + S + D + L));
        int[] arr = new int[]{1, 2, 3};
        int[][] mat = new int[2][3];
        mat[1][2] = 9;
        System.out.println("arr=" + Arrays.toString(arr) + "," + mat[1][2] + "," + arr.length);
        int[] filled = new int[3];
        for (int i = 0; i < filled.length; i++) filled[i] = i * i;
        System.out.println("filled=" + Arrays.toString(filled));
        Object[] objs = {S, CONST, new BigDecimal("1.5"), BigInteger.TEN};
        System.out.println("objs=" + Arrays.toString(objs));
        System.out.println("inc=" + inc());
        System.out.println("compound=" + compound());
        System.out.println("charArith=" + (C + 1) + "," + (char) (C + 1));
        System.out.println("boolMix=" + ((B ? 1 : 2) + (BY > 5 ? 10 : 20)));
        System.out.println("nestedTernary=" + nest(5));
        System.out.println("divZeroGuard=" + guard(0) + guard(2));
        System.out.println("stringSwitchHash=" + ("apple".hashCode() == switchHash("apple")));
        System.out.println("instanceofCast=" + io(new String("z")));
        System.out.println("arrayCopy=" + copy());
        System.out.println("prePost=" + prePost());
    }

    static int inc() {
        int i = 5;
        int a = i++;
        int b = ++i;
        i += 3;
        i -= 1;
        i *= 2;
        i /= 4;
        i %= 7;
        return a + b + i;
    }

    static String compound() {
        int x = 1;
        x &= 3;
        x |= 4;
        x ^= 5;
        x <<= 2;
        x >>= 1;
        x >>>= 1;
        long y = 10L;
        y += x;
        return x + ":" + y;
    }

    static String nest(int x) {
        return x > 10 ? "big" : x > 3 ? (x > 4 ? "mid-high" : "mid") : "small";
    }

    static int guard(int d) {
        return d == 0 ? -1 : 100 / d;
    }

    static int switchHash(String s) {
        switch (s) {
            case "apple": return "apple".hashCode();
            default: return 0;
        }
    }

    static String io(Object o) {
        if (o instanceof CharSequence) {
            CharSequence cs = (CharSequence) o;
            return "cs:" + cs.length();
        }
        return "no";
    }

    static String copy() {
        char[] src = {'a', 'b', 'c'};
        char[] dst = new char[3];
        System.arraycopy(src, 0, dst, 0, 3);
        return new String(dst);
    }

    static String prePost() {
        int[] a = {0};
        a[0]++;
        ++a[0];
        int i = 0;
        int r = i++ + ++i;
        return a[0] + ":" + r;
    }
}
