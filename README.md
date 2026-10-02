# YSHG Hook

**阅姝阁**（`com.box.dxgxx44`）增强插件 —— 下载加速 · 内置播放器 · 记录面板。

> **开源发布**（v4.14.5 定稿起）：完整源码见 [`src/yshg_hook.c`](src/yshg_hook.c)（约 3.7k 行，注释齐全）。
> 分发用二进制仍经常量段加密与符号表抹除处理（`dist/` 与 Releases 提供成品与 md5）。

作者 / 版权：**鸡巴毛**

---

## 当前版本

**v4.14.6** — 2026-10-02（**源码性能优化**）

| 文件 | 用途 | md5 |
|---|---|---|
| [dist/yshg_hook_v4146.dylib](dist/yshg_hook_v4146.dylib) | 裸插件（TrollFools 等注入用） | `500e15bc4678546a624d3de416d723c0` |
| [dist/yshg_hook_4.14.6_iphoneos-arm64.deb](dist/yshg_hook_4.14.6_iphoneos-arm64.deb) | 越狱 deb 包 | `6407cfcf4d77123d23a1e559de30838b` |
| [dist/yueshuge-hook-v4146.ipa](dist/yueshuge-hook-v4146.ipa) | 已内置插件的整包（需自签） | `6a8ce688c77dd83b21f65ff2ebc77679` |

> v4.14.6 构建链：`clang --target=arm64-apple-ios12.0.0 -fblocks -O2 -fPIC -fno-objc-arc`
> → `ld64.lld -dylib`（`-rename_section` 段搬迁）→ `ldid -S` → `llvm-strip -x`
> → `protect.py` 常量段加密（ChaCha20，密钥随机，CRC 校验，`deobf()` 运行时自解密）→ `ldid -S` 重签。

---

## 源码结构

```
src/yshg_hook.c    完整源码：流量重绑嗅探 / HLS 下载器 / TS→MP4 封装 / 播放器与 UI
dist/              成品（与 Releases 一致）
CHANGELOG.md       版本历史
```

构建链：`clang -O2 -fno-objc-arc` → `ld64.lld`（`-rename_section` 常量段搬迁）→ `ldid` → `llvm-strip` → 常量段加密。
加密/打包脚本属发布工程，不随源码发布（密钥每次构建随机）。

---

## 功能

### 下载

| 能力 | 说明 |
|---|---|
| 自动嗅探 | 抓取 app 内 m3u8 播放请求，一键入库 |
| 多任务并行 | 最多 32 队列 · 6 路并发 |
| 段级并行 | 单任务分段并行抓取，按序自动拼合 |
| 连接复用 | 专用 NSURLSession · HTTP/2 |
| 代理回退 | 直连失败自动走 app 本地代理 |
| AES-128 解密 | 支持 HLS 加密流（EXT-X-KEY） |
| TS → MP4 | 内置纯 C 重封装器，无需外部工具 |
| 断点续传 | 分段落盘，中断可续 |
| 重复抓取保护 | 同一视频正在下载时自动忽略重复请求 |

### 播放器

- 自绘控制层：渐变压暗 · 文件名 · 圆形关闭钮
- 可拖动进度条（双端时间显示）
- 播放 / 暂停 · **0.75× / 1× / 1.25× / 1.5× / 2×** 倍速（保持音调）
- 音量滑杆
- 点画面切换控制层 · 播放 3 秒后自动隐藏 · 暂停常显
- 横竖屏自适应

### 记录面板

- 双击悬浮钮呼出 · 卡片列表 · 状态徽标
- 卡片显示：文件名 / 时长 · 分辨率 · 大小 · 段数 / 完成时间
- 点行播放 · **左滑或拖动删除** · 面板可上下滑动

---

## 安装

**① TrollFools（推荐）**
注入 `yshg_hook.dylib` → 重启 app。

**② 越狱 deb**

```
dpkg -i dist/yshg_hook_4.14.5_iphoneos-arm64.deb
```

**③ 整包 IPA**
安装 `dist/yueshuge-hook-v4145.ipa`（已内置插件，需自签）。

环境要求：iOS 15.0+ / arm64，需越狱环境或 TrollStore、TrollFools 等注入环境。

---

## 使用

| 操作 | 效果 |
|---|---|
| 单击悬浮钮 | 抓取当前播放的视频 |
| 双击悬浮钮 | 打开 / 关闭记录面板 |
| 点击记录行 | 播放该文件 |
| 左滑 / 拖动记录行 | 露出删除按钮 |
| 播放中点画面 | 显示 / 隐藏控制层 |

下载目录 `Documents/yshg_dl/`　·　日志 `Documents/yshg_net.log`（超 8 MB 自动轮转）

---

## 声明

仅供个人学习研究使用，请勿商用或二次分发。