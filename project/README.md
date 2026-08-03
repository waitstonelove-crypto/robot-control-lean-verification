# lean-verify

冗余机械臂神经网络运动学控制公式的 Lean 4 + Mathlib 机器验证（推导文档速度级/加速度级 + Ma et al. IEEE TSMC 2023 源论文）。

## 复现

```bash
export ELAN_HOME="D:/AI/lean/elan"
lake build   # 8663 jobs 全绿，零 sorry，唯一 axiom 见 docs/VERIFICATION.md
```

## 文档

- `docs/formula-mapping.md`：公式 ↔ 定理对照表
- `docs/VERIFICATION.md`：验证报告（范围/假设/缺口）
- `docs/lean-work-notes.md`：执行期环境实证与数学发现
