/* サーバー（Python）が返すデータの形。フィールド名はサーバー側に合わせる（短い名前のまま） */

export type CpState = "ok" | "todo" | "copying" | "wait" | "srcbusy" | "busy" | "edited" | "old" | "err" | "off";

export interface AnaSum {
  n: number; done: number; err: number; video: number; vwarn: number; vfbad: number; vfwarn: number;
  abad: number; links: number; coi: number; auto: number; noclick: number;
}

export interface Group {
  key: string;
  files: number;
  size: number;
  pending?: number;
  pbytes?: number;
  pstart?: number;
  cats?: Record<string, number>;
  ana?: AnaSum;
  unread: number;
  cp?: Record<string, CpState>;
  cpp?: Record<string, CpState>;   // 発表ファイルだけで見た状態（どれか1つでも開ければ ok）
  last_ts?: number;
  last_kind?: string;
  recv_ts?: number;
  repl?: number;
  repl_ts?: number;
  repl_sum?: string;
  fl?: [string, string][];
  mk_recv?: boolean; mk_got?: boolean; mk_done?: boolean; mk_drop?: boolean; mk_direct?: boolean;
}

export interface Root {
  id: string;
  label: string;
  path: string;
  depth: number;
  enabled: boolean;
  online: boolean | null;
  error?: string;
  count?: number;
  pending?: number;
  scan_ms?: number;
  last_scan?: number;
  scanning?: boolean;
  n_warns?: number;
  groups?: Group[];
}

export interface EvItem { op: string; path: string; to?: string; size?: number; old_size?: number }
export interface Ev {
  id: number; ts: number; root: string; root_label: string; group: string | null; kind: string; kinds?: string[];
  title: string; summary: string; detail?: string; where?: string; items?: EvItem[]; n_items?: number;
  ana?: { file: string; text?: string; na?: string; warn?: boolean }[];
  repl?: number; while_stopped?: boolean; u?: boolean; sys?: boolean;
}

export interface OpDestSum {
  id: string; label: string; path: string; enabled: boolean; online: boolean | null; error: string;
  count: Record<string, number>; total: number;
}
export interface OpSummary {
  enabled: boolean; root?: string; venue?: string; dests: OpDestSum[]; day?: string; days?: string[];
  queue?: number; active?: { rel: string; done: number; total: number; dests?: string[] } | null; max_mbps?: number;
}

export interface UiCfg { sound: boolean; sticky: boolean; os_open: boolean; click: "app" | "both" }

export interface AppState {
  app: string; version: string; boot: string; now: number; last_event_id: number; ver: number;
  roots: Root[]; events: Ev[]; ui: UiCfg; notify: Record<string, boolean>; local: boolean; analyze: boolean;
  os: "win" | "mac" | "other"; unread_total: number; op: OpSummary; op_moved?: boolean;
}

export interface VideoInfo {
  kind: "embed" | "link" | "online"; av?: "video" | "audio"; s: number[]; name?: string; size?: number; target?: string;
  st?: "here" | "missing" | "abs" | "unc" | "online";
  fmt?: { v: "ok" | "warn" | "bad" | "unk"; container?: string; video?: string; audio?: string; res?: string; why?: string };
}
export interface Analysis {
  ok?: boolean; error?: string; na?: string; pending?: boolean; inuse?: boolean; copying?: boolean;
  slides?: number; hidden?: number[]; video?: VideoInfo[]; n_video?: number; audio?: VideoInfo[]; n_audio?: number;
  links?: { url: string; s: number[] }[]; n_links?: number; other?: { type: string; target: string; s: number[] }[];
  coi?: { s: number; kw: string; text: string }[]; auto?: [number, number][]; use_timings?: boolean; kiosk?: boolean;
  noclick?: number[];
}
export interface FolderItem {
  p: string; d: boolean; s?: number; m?: number; c?: string; mk?: string; ml?: string;
  a?: Analysis; st?: "add" | "mod" | "ren" | "pending"; ct?: number; cp?: Record<string, [CpState, string]>;
}
export interface Memo { p?: string; s?: number; m?: number; text?: string; trunc?: boolean; error?: string; pending?: boolean; more?: number }
export interface FolderDest { id: string; label: string; enabled: boolean; state?: CpState; path: string }
export interface Folder {
  root: string; group: string; label: string; path: string; items: FolderItem[]; events: Ev[]; exists: boolean; now: number;
  track?: { recv?: number; n?: number; last?: number; sum?: string } | null;
  memo?: Memo[];
  op?: { dests: FolderDest[]; pres?: { n: number; newest: string } };
}

export interface Mark { w: string; role: string }
export interface OpDestCfg { id?: string; label: string; path: string; enabled: boolean }
export interface OpDay { label: string; venue: string }
export interface OpCfg {
  enabled: boolean; root: string; venue: string; dests: OpDestCfg[]; max_mbps: number;
  days?: OpDay[]; day?: string; day_dir?: boolean; dsub?: string; _dm?: boolean;
}
export interface RootCfg { id?: string; path: string; label: string; depth: number; enabled: boolean }
export interface Config {
  roots: RootCfg[]; poll_sec: number; settle_sec: number; ignore: string[]; coi_keywords: string[]; marks: Mark[];
  notify: Record<string, boolean>; ui: UiCfg; report_while_stopped: boolean; analyze: boolean; op: OpCfg;
  [k: string]: unknown;
}
