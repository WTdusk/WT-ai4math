# WT-ai4math

本仓库收录我借助 AI 完成的数学与理论计算机科学论文，以及随论文发布的可复现检验材料。

## 论文目录

| 项目 | 论文 | 检验材料 |
| --- | --- | --- |
| [降低子序列普适性指数的游程算法](papers/subsequence-universality-deletions/) | [PDF](papers/subsequence-universality-deletions/subsequence-deletions.pdf) · [LaTeX](papers/subsequence-universality-deletions/subsequence-deletions.tex) | [Z3 脚本、依赖和结果](papers/subsequence-universality-deletions/verification/) |
| [哪些窗口长度足以判定圆环布点均衡？](papers/cycle-detection/) | [PDF](papers/cycle-detection/cycle-detection.pdf) · [LaTeX](papers/cycle-detection/cycle-detection.tex) | [Dafny 证明、Python 核验和结果](papers/cycle-detection/verification/) |

## 项目布局

每项研究在 `papers/` 下有一个独立目录。论文 PDF、LaTeX 源稿和项目说明放在项目根目录。`verification/` 保存检验代码、依赖清单及运行结果。各项目的 README 说明复现步骤和检查范围。

新增项目时，在 `papers/` 下创建以主题命名的目录，并在上方表格中添加一行。
