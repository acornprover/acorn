import { defineConfig } from "vite";
import { svelte } from "@sveltejs/vite-plugin-svelte";

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [
    svelte({
      onwarn: (warning, handler) => {
        // Ignore a11y warnings
        if (warning.code.indexOf("a11y") >= 0) return;

        // Handle all other warnings normally
        handler(warning);
      },
    }),
  ],
  base: "./",
  build: {
    outDir: "../extension/build/assistant",
    emptyOutDir: true,
  },
});
