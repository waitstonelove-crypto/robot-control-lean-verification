# 冗余机械臂控制公式 Lean 形式化验证

用 Lean 4.32.2 + Mathlib 对冗余机械臂神经网络运动学控制公式进行机器验证：

- **推导文档速度级**（伪逆/零空间/通解/误差动态/关节极限/分段梯度）
- **推导文档加速度级推广**（乘积法则/加速度伪逆/PD 误差动态/欧拉积分）
- **Li, Zhang & Jin (2017) TNNLS 稳定性定理**：控制律 (19)/Theorem 1 与控制律 (41)/Theorem 2（投影最小距离性质链、Lyapunov/LaSalle/Gronwall 论证、非凸投影集）
- 求解器数学核心（QP 凸性/一阶最优性、LVI、不动点等价、投影神经网络）

## 状态

- 构建全绿（8663 jobs）、零 `sorry`、axiom 仅 3 个（动力系统定理本体，均文档化引用来源）：
  `pnn_global_exponential_convergence`（Gao 2003）、`lasalle_global_convergence`（LaSalle 1960）、`exp_convergence`（Gronwall）
- 公式↔定理对照：`docs/formula-mapping.md`
- 验证报告（范围/假设/缺口）：`docs/VERIFICATION.md`
- 执行期环境实证：`docs/lean-work-notes.md`
- Lean 验证发现并修正的推导错误记录：`docs/formula-mapping.md` §5

## 复现

```bash
# 工具链在 D:\AI\lean\elan（Windows；ELAN_HOME=D:/AI/lean/elan）
export ELAN_HOME="D:/AI/lean/elan"
cd project
lake build
grep -rn "sorry\|admit" LeanVerify/   # 应为空
grep -rn "^axiom" LeanVerify/         # 应仅 3 个
```

## 目录

- `project/LeanVerify/`：8 个验证模块（Core / Velocity / Accel / QP_LVI_PNN / ConvergenceAxioms / Paper / Obstacle / LiZhangJin）
- `docs/`：对照表、验证报告、工作笔记、推导文档修正版
