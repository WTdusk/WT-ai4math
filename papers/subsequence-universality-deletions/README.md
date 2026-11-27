# 降低子序列普适性指数的游程算法

给定子序列普适性指数为 (I) 的字符串，本论文研究把指数降至 (k<I) 的最小带权删除代价。输入有 (r) 个游程时，求最优值的时间为 (O(r(1+\min\{k,I-k\})))，工作空间为 (O(r))。降低一级时，论文给出匹配的确定性读取下界。

- [论文 PDF](subsequence-deletions.pdf)
- [LaTeX 源稿](subsequence-deletions.tex)
- [Z3 验证脚本](verification/verify.py)
- [验证依赖](verification/requirements.txt)
- [实际运行结果](verification/results.txt)

## 复现验证

在本项目目录运行以下命令。已使用 Python 3.13 和 Z3 5.4.1 复跑。

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
```

Z3 对 16 个通用证明义务和 68 个端到端实例均返回 `unsat`。通用检查覆盖游程转移、若干归纳不变量、裁剪区间以及下界构造中的指数公式。端到端检查覆盖二元和三元字母表上长度至多 5 的适用字符串，按字母重命名去重，各位置的删除权重可取任意非负整数。任意长度下的完整最优性和复杂度论证见论文，其中超出这些检查范围的步骤使用纸面证明。

## 编译论文

安装包含 `ctex` 和 Fandol 字体的 TeX Live，在本目录运行两次 XeLaTeX 以解析交叉引用。

```sh
xelatex -halt-on-error subsequence-deletions.tex
xelatex -halt-on-error subsequence-deletions.tex
```
