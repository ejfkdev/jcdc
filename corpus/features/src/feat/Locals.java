package feat;

public class Locals {
    int field = 3;

    public static void main(String[] args) {
        new Locals().use();
    }

    void use() {
        final int captured = field * 2;
        class Local implements Runnable {
            public void run() {
                System.out.println("local:" + captured + ":" + field);
            }
        }
        new Local().run();
        Runnable r = new Local();
        r.run();
    }
}
