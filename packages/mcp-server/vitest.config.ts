import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    globals: true,
    environment: 'node',
    // Only the TypeScript sources. `dist/` holds the compiled copy of these
    // same tests, so after a build vitest collected each one twice — 212
    // "tests" for 106 real ones, and any failure reported twice. Harmless
    // locally, actively confusing in CI, where build runs before test.
    include: ['src/**/*.{test,spec}.{ts,tsx}'],
  },
});
