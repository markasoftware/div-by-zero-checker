import org.checkerframework.checker.dividebyzero.qual.*;

class Bar {

    // sum of two positives is also positive. Implementations that only think about zero vs nonzero won't be able to catch this!
    public static void sum1() {
        int alice = 5;
        int bob = 9;
        int eve = alice + bob;
        int wall_e = 5 / eve;
    }

    public static void sum2() {
        int alice = 5;
        int bob = -5;
        int eve = alice + bob;
        // :: error: divide.by.zero
        int wall_e = 5 / eve;
    }

    public static void prod1() {
        int alice = 5;
        int bob = -1;
        int eve = alice * bob;
        int wall_e = 5 / eve;
    }

    public static void prod2() {
        int alice = 5;
        int bob = 0;
        int eve = alice * bob;
        // :: error: divide.by.zero
        int wall_e = 5 / eve;
    }

    public static void div1() {
        int alice = 4;
        int bob = 5;
        int eve = alice / bob;
        // :: error: divide.by.zero
        int wall_e = 5 / eve;
    }

    public static void div2() {
        int y = 0/5;
        // want to assert that y is exactly zero, not top like it is in div1. So in addition to asserting that division by y errors, we want to assert that this doesn't error:
        int x = 1 + y;
        int z = 5/x;
        // :: error: divide.by.zero
        int w = 1/y;
    }

    // the tests in foo only check >=0, but there are other cases!
    public static void ge(int y) {
        if (y >= -5) {
            // :: error: divide.by.zero
            int x = 1/y;
        }
        if (y >= 1) {
            int x = 1/y;
        }
    }
}
