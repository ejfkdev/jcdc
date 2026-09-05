package feat;

import java.io.Serializable;
import java.util.AbstractList;
import java.util.RandomAccess;

public class OO extends Base implements Iface, Serializable {
    private static final long serialVersionUID = 1L;
    public int pub;
    protected String prot = "p";
    private double priv = 1.5;
    static int stat = 7;
    final int fin;

    static {
        stat = stat + 1;
        System.out.println("[clinit]");
    }

    {
        fin = 10;
        System.out.println("[init-block]");
    }

    public OO() {
        this(1);
    }

    public OO(int x) {
        super(x);
        pub = x * 2;
    }

    public static void main(String[] args) {
        System.out.println("ctor=" + new OO().pub + "," + new OO(5).pub);
        OO o = new OO(3);
        System.out.println("fields=" + o.pub + o.prot + o.priv + o.fin + stat);
        System.out.println("override=" + o.speak() + "," + ((Base) o).name());
        System.out.println("super=" + o.callSuper());
        System.out.println("ifaceDefault=" + o.defaultMethod() + "," + Iface.staticMethod());
        System.out.println("sync=" + o.syncMethod() + "," + OO.syncStatic());
        Inner in = o.new Inner();
        System.out.println("inner=" + in.describe() + "," + Inner.CONST);
        System.out.println("staticNested=" + StaticNested.help());
        System.out.println("anon=" + anon());
        System.out.println("anonArr=" + anonArray().length);
        System.out.println("abstractList=" + tinyList());
        System.out.println("varargs=" + varargs(1, 2, 3) + varargs());
        System.out.println("thisEscape=" + o.selfRef());
        System.out.println("shadow=" + o.shadow(9));
    }

    @Override
    String speak() {
        return "OO speaks " + pub;
    }

    @Override
    public String tag() {
        return "oo-tag";
    }

    String callSuper() {
        return super.name() + "/" + super.toString().substring(0, 2);
    }

    synchronized int syncMethod() {
        pub++;
        return pub;
    }

    static synchronized int syncStatic() {
        return stat++;
    }

    int selfRef() {
        return this == this ? this.pub : -1;
    }

    int shadow(int pub) {
        this.pub = pub;
        return this.pub + pub;
    }

    static String anon() {
        Base b = new Base(0) {
            @Override
            String speak() {
                return "anon:" + hashCode() * 0 + "x";
            }
        };
        return b.speak();
    }

    static Object[] anonArray() {
        return new Object[]{new Base(1) {
            @Override
            String speak() {
                return "b1";
            }
        }, new Iface() {
            @Override
            public String tag() {
                return "i";
            }
        }};
    }

    static int tinyList() {
        AbstractList<String> l = new AbstractList<String>() {
            final String[] data = {"a", "b"};
            public String get(int i) { return data[i]; }
            public int size() { return data.length; }
        };
        return l.size() + l.get(1).length();
    }

    static int varargs(int... xs) {
        int s = 0;
        for (int x : xs) s += x;
        return s;
    }

    class Inner {
        static final String CONST = "k";
        private int iv = 3;

        String describe() {
            return "inner:" + iv + ":" + pub + ":" + prot;
        }
    }

    static class StaticNested {
        static String help() {
            return "nested:" + stat;
        }
    }

}

abstract class Base {
    final int bx;

    Base(int x) {
        bx = x;
    }

    abstract String speak();

    String name() {
        return "Base" + bx;
    }

    @Override
    public String toString() {
        return "Base{}";
    }
}

interface Iface {
    String tag();

    default String defaultMethod() {
        return "default:" + tag2();
    }

    private String tag2() {
        return "t2";
    }

    static String staticMethod() {
        return "iface-static";
    }
}
