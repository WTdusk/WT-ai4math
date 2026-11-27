# WT-ai4math

本仓库收录我借助 AI 完成并通过形式化验证的数学与理论计算机科学论文，以及随论文发布的可复现验证材料。

## 论文目录

| 项目 | 论文 | 检验材料 |
| --- | --- | --- |
| [降低子序列普适性指数的游程算法](papers/subsequence-universality-deletions/) | [PDF](papers/subsequence-universality-deletions/subsequence-deletions.pdf) · [LaTeX](papers/subsequence-universality-deletions/subsequence-deletions.tex) | [Z3 脚本、依赖和结果](papers/subsequence-universality-deletions/verification/) |

## 项目收录规范

### 形式化验证

论文的主要结论必须有对应的形式化验证，且发布版本的全部证明义务通过后，项目才算完成并可加入论文目录。验证失败、超时、未运行或仅通过有限枚举与测试的项目暂缓收录。

### 项目打包

每个项目在 `papers/` 下使用一个独立子目录。论文 PDF、LaTeX 源稿和项目 README 放在该子目录根部。形式化验证代码、依赖清单和实际运行结果统一放在同一项目的 `verification/` 目录下。项目 README 应说明验证覆盖的结论、工具版本和复现命令。

确认论文与验证材料齐全且形式化验证通过后，在上方论文目录中添加一行。
