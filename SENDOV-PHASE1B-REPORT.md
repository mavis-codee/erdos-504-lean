# Phase-1b 状态报告 — G2 spike（Sendov 计数界）

> **私密**。落在 `E:\erdos504-grind\`（证明工作仓 scratch）。**零公开写入**：未 push、未开 PR、
> 未发评论、未改 `main` / `39e1d80` 任何字节、未触碰 `E:\mini\awards`。
> 分支：`feat/sendov-g2-spike`（本地，未 push），HEAD = `a4df531`，父 = `e5fd112`。
> 派遣日 2026-11-23，**kill switch 2026-12-07（不变）**。

---

## 0. 一句话结论

G2 spike 的**分析部分成立且可复核**，**证明部分只落地了一条引理**；一般情形
`S.card ≤ 2^(n−1) + 2^(n−3)` 的**阻塞点是外部输入（Sendov 1995/1993 全文），不是工程量**。
会话在 11-23 晚丢失，主对话已逐项复核、更正了子任务报告里的过度声称，并补做了它没跑的机检。

---

## 1. 三段式

### 1.1 已证（机器核验，公理审计通过）

| 声明 | 内容 | 证据 |
| --- | --- | --- |
| `Erdos504.angle_sum_interior` | `x` 严格位于三角形 `a b c` 内部 ⟹ `∠axb + ∠bxc + ∠cxa = 2π` | `Erdos504Formal/Erdos504SendovSpike.lean`；`lake env lean` **0 error**；公理审计 `'Erdos504.angle_sum_interior' depends on axioms: [propext, Classical.choice, Quot.sound]`（日志 `_sendov-g2_axiom_audit.log`、`_sendov-g2_build.log`） |

此外，**子任务的结构解剖经主对话逐行复核属实**（这是本轮最有价值的产出）：

| 论断 | 核对结果 |
| --- | --- |
| `2^n` 的出处 = ES1960 Lemma 4 的 `emptyCount_sum_le`（L359），在 `k = 1` 处 | ✅ L359 确为 `emptyCount_sum_le` |
| 指数落在 `hN : (Finset.univ : Finset V).card + 1 = 2 ^ n`（L2782） | ✅ 逐字一致 |
| `−2` 的出处 = **两个互相不同的孤立点**各贡献 `2^{ν(p)}−1 ≥ 1`（内点 L2404 + 凸包顶点 L1854） | ✅ L2787 注释 "Each isolated point contributes at least `1`"、`he1` L2788 |
| `scb_of_no_extremal`（L845）把「`2^n−1` 不可达」转成 `|S| ≤ 2^n−2` | ✅ 签名一致 |
| `hull_card_le`（L1662）给 `m ≤ 2n−1`（**线性**、且**锐**：正 `(2n−1)` 边形满足 `max angle < π(1−1/n)`） | ✅ 签名一致，且锐性论证正确 |
| 六条候选路线的判定（A 多造孤立点 / B 半化递归 / C 凸位置 / D 少扇区 / E 改凸包界 / F ES Thm 2） | ✅ 逐条复核**全部成立**，见 §1.3 |

### 1.2 未证

| 目标 | 状态 |
| --- | --- |
| `sendov_counting_bound_large`（一般情形：`全角 < π(1−1/n)` ⟹ `|S| ≤ 2^(n−1)+2^(n−3)`） | **未证** |
| `exists_angle_ge_two_pi_div_three_of_interior`（内点 ⇒ 某角 `≥ 2π/3`） | **未写入**（数学路线已定，见 §2.2） |
| `sendov_counting_bound_n3`（`n = 3` 特例：`全角 < 2π/3` ⟹ `|S| ≤ 5`） | **未写入**（数学路线已定，见 §2.2） |

> **重要更正**：子任务的自述文件 `SENDOV-G2-SPIKE.md` §4 原把后两条列为「已证」，
> 但**它们从未写进 Lean 文件**（会话在写完 `angle_sum_interior` 后丢失）。
> 主对话已加更正横幅并修正该表；§1 的解剖与 §3 的路线评估保持原样（已复核为真）。
> 另：子任务 §6 引用的两份日志**当时并不存在** —— 机检从未跑过；现已由主对话补做并落盘。

### 1.3 卡点（一般情形缺什么数学事实）

按路线 A 的精确形式，闭合一般情形需要：

1. **（记账）** 在 ES Lemma 4 的亏损账本上做到
   `Σ_{p∈S} (2^{ν(p)} − 1) ≥ 3·2^(n−3)`。
   现有几何只能提供 **2** 个单位（一个内点 + 一个凸包顶点）。而：
   - 凸包顶点总数 `≤ 2n − 1`（**线性**，且界是锐的）；
   - **内点本来不是孤立点**（内点方向充满整圈，`ν = 0`），现有证明里内点之所以孤立，
     纯粹是**为它专门做的一次整体旋转**的副作用 —— 这种副作用一次只能救一个点。

   ⇒ 要凑出指数多个「可同时孤立」的顶点，必须引入**全新几何装置**（即 Sendov 的
   GC / perfect GC），而其定义与引理**在付费墙后**。
2. **（几何，路线 B 等价形式）** 半化引理：全角 `< π(1−1/n)` ⟹ 存在 `≥ |S|/2` 的子集，
   其全角 `< π(1−1/(n−1))`。数值上与 Sendov 的 `5·2^(n−3)` 完全吻合（基例 5、每步加倍），
   但它**本身是一条新的全局角度结构命题**，ES1960 的全部器械（扇区着色 + Lemma 4）
   产不出这种「一半点集、阈值更紧」的结构；公开文献也**没有**「半化」论证的迹象
   （更可能是数值巧合）。沿此路走等于重做 Sendov 的工作。
3. **（分类）** 极值构型（"perfect GC"）的刻画与锐性 —— 属 G4，本 spike 范围外。

**已排除的路线**（复核后确认死路，勿再试）：
- **D 少扇区**：假设「全角 `< π(1−1/n)`」**不蕴含** `P_m`（`m < n` ⟹ `π(1−1/m) < π(1−1/n)`），
  偶分割无法套用。
- **E 改凸包界**：界 `m ≤ 2n−1` **是锐的**（正 `(2n−1)` 边形满足假设），任何更小的上界都是假的。
- **F ES Theorem 2**（缺陷角界）：在 `N = 5·2^(n−3)+1` 处给出的阈值比 `π(1−1/n)` 略小，
  无法反推所需结论。

---

## 2. 下一步

### 2.1 判定

- **G2 一般情形 = 外部输入阻塞（STOP-pending-source）**：要再进一步，必须拿到
  **Se95 全文**（Acta Math. Hungar. **69** (1995), 27–46，DOI 10.1007/BF01874605；
  需要的是主定理证明所在章节：GC / configuration of circles / perfect GC 的定义与
  「极值基数」引理）**或** **Se93 全文**（C. R. Acad. Bulgare Sci. **46** (1993), 27–30，
  4 页；主定理 1993 年已定案，可能已含该计数界的证明骨架）。
  在此之前，**继续 grind 一般情形属于硬扛**，不予进行。
- **n = 3 特例 = 可做且值得做**（不依赖付费墙），路线已定、只差两步形式化（见 §2.2）。

### 2.2 已派遣的续作（n = 3 特例，kill switch 仍为 2026-12-07）

在既有分支 `feat/sendov-g2-spike` 上续作，**只做两件事**：

1. `exists_angle_ge_two_pi_div_three_of_interior`：`q` 不是 `conv S` 的顶点（一般位置）⟹
   存在 `p, r ∈ S` 使 `∠pqr ≥ 2π/3`。
   路线：`angle_sum_interior` + 包含 `q` 的三角形 + 三角和 `2π` ⟹ 三个角中一个 `≥ 2π/3`。
2. `sendov_counting_bound_n3`：全角 `< 2π/3` ⟹ `|S| ≤ 5`。
   路线：上一条 ⟹ `S` 无内点 ⟹ `S` 处于凸位置 ⟹ `|S| = m ≤ 2·3 − 1 = 5`（用已证的
   `hull_card_le`）。

**这一特例的价值是实的**：Sendov 在 `n = 3` 的界是 `|S| ≤ 5`，而我们已证的
`strictCountingBound` 在 `n = 3` 只给 `|S| ≤ 6` —— 即 `n = 3` 处严格更强。
**但它不构成 G2 的闭合**（一般情形仍未证），按规则 a 也不足以单独构成可提交成果。

**续作红线**：不碰一般情形、不碰 G3/G4、不 push、不改 `main`/`39e1d80`；
若 n = 3 也卡住，立即出 STOP 报告并停手。

---

## 3. 对 Phase-0 预测的印证

Phase-0 报告（`SENDOV-PHASE0.md`）§4.1 估计 G2 为「3–8 周、置信度中低，需原文细节」，
并把「原文不可得」列为 **R2（高等级）**。本轮结果与该预测一致：

- 路线评估确认：**现有器械只能做到 `−2`**，
  「把界从 `2^n−2` 压到 `5·2^(n−3)`」需要的是**新几何装置**，不是把现有证明写得更细；
- 这独立地印证了 Phase-0 的结论：**Sendov 全 N 的瓶颈是文献可得性，不是形式化难度**。
  → 建议把「取得 Se95/Se93 全文」当作下一项**采购/馆际互借**任务，而不是继续投入 Lean 工时。

---

## 4. 红线核对

| 红线 | 状态 | 证据 |
| --- | --- | --- |
| 不 push / 不 PR / 不评论 | ✅ | 本轮只做本地提交 `a4df531`；`origin/main` 仍 `39e1d80`；`fork` 远端未动 |
| 不改 `main` / `39e1d80` 字节 | ✅ | `main` = `39e1d80`；新提交全在 `feat/sendov-g2-spike` |
| 不以 `sorry` 冒充闭合 | ✅ | 唯一声明 `angle_sum_interior` 无 sorry 且已审计；未写的两条在文件头与报告里明写「未写入」 |
| 不自行开工 G3 / G4 | ✅ | 未涉及；已在派遣书与本报告中继续标注 |
| 交付 build log + 公理审计（含 sorryAx 显式） | ✅ | `_sendov-g2_build.log`、`_sendov-g2_axiom_audit.log`；本文件无 sorry 目标 |
| kill switch 2026-12-07 | ✅ | 不变；续作按同一截止日 |

## 5. 产出物清单（`E:\erdos504-grind`）

| 文件 | 状态 |
| --- | --- |
| `SENDOV-G2-SPIKE.md` | 已提交（`821a831`），后由 `a4df531` 加更正横幅并修正 §4 表 |
| `Erdos504Formal/Erdos504SendovSpike.lean` | 已提交（`a4df531`）；**仅一条声明**，已核验 |
| `_sendov-g2_build.log`、`_sendov-g2_axiom_audit.log` | 已提交（`a4df531`） |
| `SENDOV-PHASE1B-REPORT.md` | 本文件（未跟踪 scratch） |
| `_scratch_fr2..5.lean`、`_scratch_finrank.lean` | 子任务遗留的 `Module.finrank ℝ (vectorSpan ℝ X) ≤ 2` 尝试，未提交、未纳入结果 |

---

## 6. n=3 特例闭合（主对话零积分接管，2026-11-24）

MiniMax 积分断于 n=3 机检红（13 处形式化笔误）之后。主对话零积分接管，逐处修正
（`lt_or_ge` 分支方向、`rw [hconv]` 方向、`Finset.convexHull_eq` 改用 `rw … at`、
`Ne.symm` 方向、`zero_add`、`False.elim`、`hn := by norm_num`、`set_option` 位置、
`linarith [Real.pi_pos]`），**不改动数学路线**。终核 `_sendov-n3_build6.log`：
**0 error、0 warning**，五条声明公理审计全部恰为 `[propext, Classical.choice, Quot.sound]`，
**无 `sorryAx`**：

| 声明 | 内容 |
| --- | --- |
| `convexHull_eq_convexHull_extremePoints` | Minkowski：凸包=其极点之凸包 |
| `angle_eq_pi_of_combination` | 线段内点处角=π |
| `exists_angle_ge_two_pi_div_three_of_interior_point` | 三角形内点三角必有一角≥2π/3 |
| `exists_angle_ge_two_pi_div_three_of_interior` | 非凸包顶点必见≥2π/3 角 |
| `sendov_counting_bound_n3` | 全角<2π/3 ⟹ `S.card ≤ 5` |

**价值与边界**：n=3 处 Sendov 界 5 严格强于已证 `strictCountingBound` 的 6（正五边形达 5）。
**但按规则 a 仍不足以单独构成可提交成果**（一般情形未证）；一般情形 G2 仍=付费墙阻塞
（§2.1 不变）。本轮**零公开写入**：仅本地提交，未 push、未改 `main`/`39e1d80`。
