// Add this at the top of the file (after structs, before functions)
__constant float GAUSSIAN_KERNEL_5X5[25] = {
    0.003f, 0.013f, 0.022f, 0.013f, 0.003f,
    0.013f, 0.059f, 0.097f, 0.059f, 0.013f,
    0.022f, 0.097f, 0.159f, 0.097f, 0.022f,
    0.013f, 0.059f, 0.097f, 0.059f, 0.013f,
    0.003f, 0.013f, 0.022f, 0.013f, 0.003f
};
