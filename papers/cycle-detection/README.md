# 哪些窗口长度足以判定圆环布点均衡？

论文给出一组窗口长度足以判定循环二元词均衡的充要条件，并将均衡性应用于分析相关失效下的首次探测时间。

- [论文 PDF](cycle-detection.pdf)
- [LaTeX 源稿](cycle-detection.tex)
- [Dafny 证明入口](verification/formal/Paper.dfy)
- [Python 枚举核验](verification/verify.py)
- [实际运行结果](verification/results.txt)

## 复现检验

在本项目目录运行以下命令。Python 脚本仅使用标准库。以下命令使用 Dafny 4.11.0。将 `<z3-executable>` 替换为你的 Z3 可执行文件路径。

```sh
python verification/verify.py
dafny verify --verify-included-files --solver-path <z3-executable> --cores 4 verification/formal/Paper.dfy
```

Python 枚举核验已通过，覆盖圈长至多 12 的判定条件，以及圈长至多 8 时按失效向量循环平移计算的漏检概率。Dafny 源码针对窗口判定充要条件，包含必要性反例的构造。本次用 Dafny 4.11.0 复跑时出现证明义务错误和超时，未通过全量验证。相关失效下首次探测最优性的通用证明见论文。

## 编译论文

安装包含 `ctex`、Fandol 字体和 TikZ 的 TeX Live。在本项目目录运行两次 XeLaTeX。

```sh
xelatex -halt-on-error cycle-detection.tex
xelatex -halt-on-error cycle-detection.tex
```
