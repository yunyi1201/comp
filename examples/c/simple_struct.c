struct A {
    int a;
    double b;
};

int main(int argc) {
    struct A a = {1, { 1, 2.0 }};
    return 1;
}
