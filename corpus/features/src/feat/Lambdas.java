package feat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntSupplier;
import java.util.function.Supplier;
import java.util.stream.Collectors;

public class Lambdas {
    static int sideEffect = 0;

    public static void main(String[] args) {
        System.out.println("simple=" + apply(x -> x * 2, 21));
        System.out.println("twoArgs=" + apply2((a, b) -> a + b + "!", "x", "y"));
        System.out.println("noArgs=" + supply(() -> 42));
        System.out.println("voidLambda=" + consume(v -> sideEffect += v, 5) + sideEffect);
        System.out.println("block=" + apply(x -> {
            int y = x + 1;
            y *= 3;
            return y - 2;
        }, 10));
        System.out.println("capture=" + apply(capture(3), 10) + "," + sideEffect);
        System.out.println("methodRefStatic=" + apply(Lambdas::doubleIt, 5));
        System.out.println("methodRefInstance=" + apply(new Lambdas()::tripleIt, 5));
        System.out.println("methodRefUnbound=" + apply(String::length, "abcd"));
        System.out.println("ctorRef=" + supply(ArrayList<String>::new).size());
        System.out.println("nested=" + apply(y -> apply(z -> z + 1, y), 1));
        List<String> words = Arrays.asList("bb", "a", "ccc");
        List<String> sorted = words.stream()
                .sorted(Comparator.comparingInt(String::length))
                .map(String::toUpperCase)
                .filter(s -> s.length() > 1)
                .collect(Collectors.toList());
        System.out.println("stream=" + sorted);
        words.forEach(w -> System.out.print("[" + w + "]"));
        System.out.println();
        IntSupplier counter = counterSupplier();
        System.out.println("counter=" + counter.getAsInt() + counter.getAsInt() + counter.getAsInt());
        System.out.println("condLambda=" + apply(flag(true), 2));
    }

    static <T, R> R apply(Function<T, R> f, T t) {
        return f.apply(t);
    }

    static <A, B, R> R apply2(BiFunction<A, B, R> f, A a, B b) {
        return f.apply(a, b);
    }

    static <T> T supply(Supplier<T> s) {
        return s.get();
    }

    static <T> int consume(Consumer<T> c, T t) {
        c.accept(t);
        return 1;
    }

    static int doubleIt(int x) {
        return x * 2;
    }

    int tripleIt(int x) {
        return x * 3;
    }

    static Function<Integer, Integer> capture(int base) {
        int factor = base + 1;
        final String tag = "t" + base;
        return x -> {
            sideEffect = tag.length();
            return x * factor + base;
        };
    }

    static IntSupplier counterSupplier() {
        int[] state = {0};
        return () -> ++state[0];
    }

    static Function<Integer, Integer> flag(boolean b) {
        return b ? (x -> x + 100) : (x -> x - 100);
    }
}
