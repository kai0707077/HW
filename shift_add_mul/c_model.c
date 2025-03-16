uint64_t shift_add_multiply(uint32_t a, uint32_t b) {
    uint64_t product = 0;
    printf("=============================================\n");
    printf("Starting multiplication:\n");
    printf("    a = %u (0x%08X)\n", a, a);
    printf("    b = %u (0x%08X)\n", b, b);

    for (int i = 0; i < 32; i++) {
        if (b & (1U << i)) {
            uint64_t shifted = ((uint64_t)a) << i;
            printf("Iteration %2d: b[%2d] = 1 -> shifted value = a << %2d = 0x%016llX\n",
                   i, i, i, (unsigned long long)shifted);
            product += shifted;
            printf("Iteration %2d: Partial sum = 0x%016llX\n", i, (unsigned long long)product);
        } else {
            printf("Iteration %2d: b[%2d] = 0 -> no addition\n", i, i);
        }
    }
    printf("Final product = 0x%016llX\n", (unsigned long long)product);
    printf("=============================================\n");
    return product;
}
