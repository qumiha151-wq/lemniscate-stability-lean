# 论文与 Lean 对照表（未完成版）

目标是逐条比对实际命题、量词及假设，不能把有限维或条件性结论误当成原论文主定理。
下面的名称指代码中的陈述，是否编译成功以当前源文件哈希对应的 build.json 为准。

| 原稿内容 | Lean 陈述 | 目前的对应边界 |
| --- | --- | --- |
| 第 2 节线性化常数与 Fourier 系数 | `linearization_zero_order`, `linearization_first_order`, `fourier_coefficient_identity` | 证明代数恒等式；变化公式本身尚未形式化 |
| 第 2 节旋转模 `A(qq_x)=0` | `rotation_kernel` | 对满足 ODE 和第一积分的实际可微函数证明；尚需把这些函数识别为几何 Bernoulli 曲率 |
| 带权行引理 | `weighted_row_dissipation`, `complex_weighted_row_dissipation` | 任意有限指标集的实或复二次型；须继续证明 Fourier 型表示及 H2 稠密延拓 |
| 9 项余弦低频比较及其完整行意义 | `CoarseArithmetic.cosine_rows`, `cosine_low_rows_dissipative` | 从有理公式的内核计算，连接到系数公式定义的矩阵全行：前 20 项区间估计加全部加权尾项；矩阵与几何算子的识别仍待完成 |
| 区间算术 | `CoarseArithmetic.mul_sound`, `absUpper_sound`, `reciprocalPositive_sound`, `sqrt_enclosure_sound` | 已证明实数的四则、正倒数及平方根包络；整数外舍入还需补齐 |
| 几何级数尾公式 | `tail1_sound`, `tail2_sound`, `tail3_sound`, `hasSum_geometric_moment_four`, `hasSum_geometric_moment_five`, `hasSum_geometric_moment_six` | 以 `HasSum` 证明零至六阶矩和前三阶移位尾和的精确有理式；实际矩阵及约束项的控制还需逐项连接 |
| 正频 Fourier 系数包络 | `CoarseArithmetic.positive_fourier_enclosure` | 由参数有理界证明所有正整数频率的系数公式包络；Jacobi Fourier 展开仍需形式化 |
| 常数 Fourier 系数及无限尾项 | `CoarseArithmetic.summable_fourier_tail`, `fourier_tail_bound`, `constant_fourier_enclosure` | 证明整个系数级数收敛、任意正截断点的尾界及前四项加全尾的常数项包络；仍以参数有理界为假设 |
| 余弦矩阵条目的区间控制 | `CoarseArithmetic.cosine_matrix_enclosure` | 从收敛级数定义系数，逐项证明实矩阵公式被计算使用的区间包围；矩阵与几何微分算子的 Fourier 表示仍需识别 |
| `Q=exp(-π)` 的粗有理界 | `CoarseArithmetic.coarse_nome_bounds` | 使用数学库已证明的圆周率界与指数级数余项界；不依赖浮点近似 |
| theta 级数的粗参数界 | `CoarseArithmetic.theta_enclosure`, `actual_nome_theta_r_bounds` | 控制完整 theta 级数及其负四次方；与 `(π/(2K))²` 的椭圆积分恒等式尚待形式化 |
| 参数界在矩阵中的实例化 | `CoarseArithmetic.theta_nome_cosine_matrix_enclosure` | 在 `Q=exp(-π)` 和 theta 参数下消除数值参数假设；不能据此宣称已证明矩阵就是原几何算子的表示 |
| 正弦约束中的 `ρ²<(87/500)²` | `CoarseArithmetic.sine_constraint_series_bound`, `theta_nome_sine_constraint_bound` | 控制全部 `j≥2` 的系数比平方级数并证明收敛；旋转系数的几何识别仍需形式化 |
| 正弦正交约束到首模及耗散估计 | `CoarseArithmetic.sine_constraint_first_mode`, `sine_constraint_energy_bound` | 已构造复系数 `ℓ²` 尾向量并应用 Cauchy–Schwarz；`-75` 结论仍假设尾块 `-100` 和耦合 `63` 所给的能量不等式，实际算子的这些界尚待连接 |
| 统一指数系数上界及和、差频率比较 | `CoarseArithmetic.theta_nome_coefficient_majorant`, `common_index_coefficient_majorant` | 对全部正频率证明 `H j qb^j` 上界；用离散单调性把和频率项控制为差频率项 |
| 非对角矩阵条目尾界 | `CoarseArithmetic.positive_frequency_upper_tail`, `cosine_upper_tail_all`, `cosine_lower_tail` | 正频公式的两种符号均受 `C (2j+l)^2 l qb^l` 控制；余弦零模单独处理其 `√2` 因子，并用矩阵对称性得到下三角界 |
| 完整上三角尾行的绝对收敛及上界 | `CoarseArithmetic.positive_frequency_tail_bound`, `cosine_tail_bound_all` | 从任意正截断点开始求和，以上述条目界和前三阶几何矩得到精确有理上界；包含余弦零行 |
| 余弦行的实际几何权重与全尾界 | `CoarseArithmetic.weight_pos`, `cosine_weighted_tail_bound`, `cosine_weighted_lower_majorant` | 证明所有权重严格正，并包含三个特殊低频权重；上、下频率方向分别使用底数 `qb*a` 与 `qb/a` |
| 偶频余弦高频行与全部行的统一界 | `CoarseArithmetic.cosine_high_row_quartic_bound`, `cosine_all_rows_dissipative` | 将完整高频行连接到已认证四次多项式，再与九个低频行合并；所有行级数收敛且严格小于 `-21/4` |
| 偶频余弦矩阵的复二次型耗散 | `CoarseArithmetic.cosine_finite_form_dissipative` | 对任意有限指标集和任意复系数，实际系数矩阵二次型不超过 `-21/4` 倍质量；随后由 `cosine_h2_form_dissipative` 推广到 H² 系数域，几何 Fourier 表示识别仍待完成 |
| 偶频余弦形式的 H² 系数域收敛 | `CoarseArithmetic.cosine_energy_summable`, `cosine_absolute_tsum_bound` | 从具体矩阵条目界和 H² 加权平方可和性证明整个双级数绝对收敛；收敛不是额外假设 |
| 偶频余弦形式的无限序列耗散 | `CoarseArithmetic.cosine_h2_form_dissipative`, `h2_coefficients_iff_even_frequency` | 对 H² 加权复系数序列证明完整双级数的 `-21/4` 耗散；权重对应频率 `2j`，周期 Sobolev 域由后续模块识别，几何算子的 Fourier 表示仍待识别 |
| 归一化偶频余弦展开与周期 L² 范数 | `even_cosine_orthonormal`, `circle_even_cosine_hasSum`, `circle_even_cosine_norm_sq` | 使用圆周上总质量为 1 的 Haar 测度，将复 ℓ² 系数等距嵌入实际 L² 函数空间；不声称该余弦族张成整个 L² 空间 |
| 无限展开后的 Fourier 频率与归一化 | `circle_even_cosine_coeff_zero`, `circle_even_cosine_coeff_pos`, `circle_even_cosine_coeff_neg`, `circle_even_cosine_coeff_odd` | 零频系数为 `v 0`；正偶频 `2j` 的系数为 `v j / √2`，负频反射相等，全部奇频为零；系数通过连续线性泛函与收敛的 L² 级数相连 |
| 系数能量与实际周期函数的质量 | `h2_circle_function_energy_bound` | 对 H² 加权系数构造的圆周函数，系数二次型不超过 `-21/4` 倍 L² 范数平方；后续模块证明周期 Sobolev 导数刻画，尚未识别为几何微分算子的二次型 |
| H² 系数域与二阶频率乘子 | `h2_coefficients_iff_second_l2` | 双向等价：H² 加权平方可和，当且仅当原系数和 `-(2j)² v_j` 都属于 ℓ²；此处仍为系数域陈述 |
| 二阶导数候选函数与有限截断 | `h2_circle_angular_second_fourier`, `h2_circle_graph_approximation`, `h2_circle_angular_second_symmetric` | 在实际圆周 L² 中构造候选函数，其全部 Fourier 系数为 `-n²` 乘原系数；函数和候选二阶导数的有限截断同时收敛，且该乘子对称；后续 `PeriodicWeakSecond` 处理其弱导数意义 |
| 有限 Fourier 和的经典导数 | `cosine_mode_value_ae`, `hasDerivAt_cosine_partial`, `hasDerivAt_cosine_partial_first` | 核对 L² 模的具体函数代表及有限和的一、二阶导数；任意周期 T 保留 `(2π/T)²` 因子，论文角坐标为 T=2π |
| 任意经典周期函数的 Fourier 求导 | `fourierCoeff_classical_deriv`, `fourierCoeff_classical_second` | 由周期端点消去与微积分基本定理证明所有整数频率的求导公式，包括零频；不假设 Fourier 级数逐点可微 |
| H² 余弦函数的弱二阶导数 | `h2_circle_second_weak`, `h2_circle_second_integration_by_parts` | 对所有周期 C² 测试函数证明真实 Haar 积分的分部积分关系；二阶导数在 L² 中构造，周期尺度明确；一、二阶 Sobolev 域等价由下述后续模块处理 |
| 弱二阶导数的刻画与唯一性 | `weak_circle_second_iff_fourier`, `weak_circle_second_unique` | 在整个周期 L² 空间中，C² 测试恒等式与全部 Fourier 系数的二阶乘子公式等价，因此满足该弱导数关系的 L² 函数唯一 |
| 弱一阶导数的刻画与唯一性 | `weak_circle_deriv_iff_fourier`, `weak_circle_deriv_unique` | 对所有周期 C¹ 测试函数定义弱导数，并与全部 Fourier 系数的 `i(2π/T)n` 乘子公式双向对应；核对复内积约定下的负号 |
| 二阶弱导数与逐次弱求导 | `weak_circle_second_iff_deriv_chain`, `h2_circle_derivative_chain` | 从原函数和弱二阶导数的 L² 性质推出一阶乘子系数属于 ℓ²，构造一阶导数；证明再次弱求导得到给定二阶导数 |
| 周期 H² 的完整 Fourier 刻画 | `circle_h2_iff_weighted_fourier` | H² 在此明确定义为存在两次逐次 L² 弱导数；在整个周期 L² 空间中，等价于权重 `1+((2π/T)n)²` 乘 Fourier 系数后的平方可和性 |
| 余弦 Sobolev 域的双向识别 | `circle_cosine_mem_h2_iff`, `circle_cosine_sobolev_energy_bound` | 对任意 ℓ² 余弦系数，合成函数属于上述 H² 当且仅当满足原加权系数条件；因此可由弱导数条件调用 `-21/4` 系数耗散界，仍不等同于几何算子二次型 |
| 曲率四次幂的 Fourier 恒等式 | `circle_profile_square_second`, `circle_profile_fourth_fourier`, `circle_profile_fourth_mean` | 从显式 ODE 与第一积分推出 `(q²)''=1−3q⁴`，进而得到全部 Fourier 系数与均值 `1/3`；尚未构造并识别具体 Jacobi 曲率 |
| 四阶微分表达式与双向 Fourier 矩阵 | `circle_symmetric_expression_coordinate`, `paper_symmetric_mode_fourier` | 核对真实坐标导数和乘积求导，推导频率差条目；本模块只处理论文所写微分表达式，不等于完成无界算子的伴随、定义域或全谱识别 |
| 归一化余弦模的经典求导与算子作用 | `circle_cosine_jet_deriv`, `circle_cosine_jet_zero_l2`, `circle_symmetric_cosine_fourier` | 对所有阶数证明经典导数链，将零阶函数与已有 L² 模等价类对应，并计算四阶表达式的像 |
| 实际 L² 内积中的余弦矩阵公式 | `circle_cosine_matrix_positive`, `circle_cosine_matrix_zero_zero`, `circle_cosine_matrix_zero_positive`, `circle_cosine_matrix_positive_zero` | 在系数反射对称及经典二阶可微条件下，证明正频率公式、零模对角 `−42` 和两侧 `√2` 例外项；周期尺度为 `(2π/T)²`，与 theta 定义的已认证系数矩阵的识别仍待完成 |
| 微分表达式矩阵与认证矩阵的条件连接 | `circle_cosine_matrix_eq_coefficients` | 若实际系数 Fourier 序列满足 `fourierCoefficient r Q j` 公式，反射对称且 `(2π/T)²=r`，则对所有 `j,k`，实际 L² 内积条目等于 `cosineMatrixEntry r Q j k`；这些前提尚须对具体 Jacobi 曲率证明 |
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
