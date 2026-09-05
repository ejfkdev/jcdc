package feat;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Java 7 feature coverage: string switch, try-with-resources, multi-catch,
 * diamond operator, binary/underscore literals. Compiles with javac 7.
 */
public class Legacy7 {
    public static void main(String[] args) throws Exception {
        System.out.println("sw=" + strSwitch("a") + strSwitch("b") + strSwitch("z") + strSwitch(null0()));
        System.out.println("nums=" + (0b1010 + 1_000_000 / 1_000));
        System.out.println("diamond=" + diamond());
        System.out.println("twr=" + twr());
        System.out.println("multi=" + multi(1) + "," + multi(0));
        System.out.println("map=" + mapIter());
    }

    static String null0() {
        return "a";
    }

    static String strSwitch(String s) {
        switch (s) {
            case "a":
                return "A";
            case "b":
            case "c":
                return "BC";
            default:
                return "?";
        }
    }

    static String diamond() {
        List<List<String>> ll = new ArrayList<>();
        List<String> l = new ArrayList<>();
        l.add("x");
        ll.add(l);
        return ll.get(0).get(0) + ll.size();
    }

    static String twr() throws IOException {
        File f = File.createTempFile("jcdc", ".tmp");
        String r;
        try {
            try (FileInputStream in = new FileInputStream(f)) {
                r = "read" + (in.read() == -1 ? "EOF" : "B");
            }
        } finally {
            f.delete();
        }
        return r;
    }

    static String multi(int x) {
        try {
            if (x > 0) {
                throw new IOException("io");
            }
            return "ok";
        } catch (IllegalStateException | IOException e) {
            return "caught:" + e.getClass().getSimpleName();
        }
    }

    static String mapIter() {
        Map<String, Integer> m = new HashMap<>();
        m.put("a", 1);
        m.put("b", 2);
        int t = 0;
        for (Map.Entry<String, Integer> e : m.entrySet()) {
            t += e.getValue();
        }
        return "t" + t;
    }
}
