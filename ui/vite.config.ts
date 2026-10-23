import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import tailwindcss from "@tailwindcss/vite";
import { viteSingleFile } from "vite-plugin-singlefile";

// 1つのHTMLにまとめて、Pythonの中に埋め込む（会場ではネットにつながらなくても動くように、外部から何も読み込まない）
export default defineConfig({
  plugins: [react(), tailwindcss(), viteSingleFile()],
  build: { target: "es2020", cssCodeSplit: false, assetsInlineLimit: 100000000, minify: "esbuild", sourcemap: false },
  server: { proxy: { "/api": "http://127.0.0.1:8897" } },
});
