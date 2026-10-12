# 论文与 Lean 对照表（未完成版）

目标是逐条比对实际命题、量词及假设，不能把有限维或条件性结论误当成原论文主定理。
下面的名称指代码中的陈述，是否编译成功以当前源文件哈希对应的 build.json 为准。

| 原稿内容 | Lean 陈述 | 目前的对应边界 |
| --- | --- | --- |
| 第 2 节线性化常数与 Fourier 系数 | `linearization_zero_order`, `linearization_first_order`, `fourier_coefficient_identity` | 证明代数恒等式；变化公式本身尚未形式化 |
| 第 2 节旋转模 `A(qq_x)=0` | `rotation_kernel` | 对满足 ODE 和第一积分的实际可微函数证明；尚需把这些函数识别为几何 Bernoulli 曲率 |
| 带权行引理 | `weighted_row_dissipation`, `complex_weighted_row_dissipation` | 任意有限指标集的实或复二次型；须继续证明 Fourier 型表示及 H2 稠密延拓 |
| 9 项余弦低频比较 | `CoarseArithmetic.cosine_rows` | 直接对论文的有理公式做内核计算；须继续证明实际 Fourier 系数落在给定包络 |
| 区间算术 | `CoarseArithmetic.mul_sound`, `absUpper_sound` | 已明确解释为实数的区间包含；倒数、平方根和整数外舍入还需补齐 |
| Bernstein 展开与正性 | `degree_six_conversion`, `degree_four_conversion`, `odd_rows_positive_on_interval` | 已连接奇频有理系数与实六次多项式，在整个 `[0,1/2]` 区间得到下界；尚需连接多项式与实际 Fourier 行 |
| 84 项奇频及 12 项零参数比较 | `OddArithmetic.all_odd_bernstein_comparisons`, `all_odd_zero_comparisons` | 从完整有理公式计算；不能单独代表其无限尾界的分析意义 |
| 高频四次多项式方法 | `HighFrequency.cosine_high_bound`, `sine_high_bound`, `odd_high_bound`, `even_high_bound` | 已实例化四个实际多项式，内核从定义计算起点比较并证明所有阈值外实数上的上界；须证明实际 Fourier 行被这些多项式控制 |
| 旋转核与广义核 | `NeutralCoerciveOperator.kernel_is_neutral`, `no_generalized_neutral` | 对显式定义域上的算子，在正交补耗散假设下成立；实际算子耗散尚未连接 |
| 非零特征值实部界 | `NeutralCoerciveOperator.nonzero_eigenvalue_bound` | 特征值界；全谱结论另需紧预解算子等分析桥梁 |
| 中性因子精确消去 | `exact_center_cancellation`, `exact_cross_cancellation` | 标量块恒等式；还需证明变换可逆、保持定义域及有限秩范数误差 |
| 任意重数谱隙 | `multiple_cover_gap` | 仅有参数下界到平方谱隙的实数推论；Bloch 直和和谱隙阶数尚未形式化 |
| 加权局部理论 | `weighted_critical_exponents` | 仅验证三个指数等式；不是 PSW 存在唯一性定理 |
| 非线性正常稳定性 | 尚无完整 Lean 定理 | PSZ、最大正则性、平衡流形及平滑论证均有待形式化 |
| 曲率小量到 H2 正常图 | 尚无完整 Lean 定理 | 几何和 Sobolev 复合论证有待形式化 |
| 物理时间衰减换算 | `physical_decay_identity`, `normalizedTime_at_unit_scale` | 已证明指数衰减的精确幂次换算及等待时间下界；几何解的衰减尚未建立 |
| 主定理 1.1 | 尚无完整 Lean 定理 | 不得宣称已获 Lean 证明 |

最终核对还须检查：M 的整数和正性条件、旋转与平移的选择、重参数化的定向、
固定小邻域与逐阶定量小邻域的不同量化、物理时间起点、各常数依赖，以及
所有谱/算子定理使用的定义域。发现不一致时须修订论文并重新核查相关证明。
