# 论文与 Lean 对照表（未完成版）

目标是逐条比对实际命题、量词及假设，不能把有限维或条件性结论误当成原论文主定理。
下面的名称指代码中的陈述，是否编译成功以当前源文件哈希对应的 build.json 为准。

| 原稿内容 | Lean 陈述 | 目前的对应边界 |
| --- | --- | --- |
| 第 2 节线性化常数与 Fourier 系数 | `linearization_zero_order`, `linearization_first_order`, `fourier_coefficient_identity` | 证明代数恒等式；变化公式本身尚未形式化 |
| 第 2 节旋转模 `A(qq_x)=0` | `rotation_kernel` | 对满足 ODE 和第一积分的实际可微函数证明；尚需把这些函数识别为几何 Bernoulli 曲率 |
| 带权行引理 | `weighted_row_dissipation`, `complex_weighted_row_dissipation` | 任意有限指标集的实或复二次型；余弦扇区的 Fourier 型表示及 H² 延拓见后续条件连接，其他扇区仍待处理 |
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
| 有限余弦函数的实际能量估计 | `circle_polynomial_energy_eq_matrix`, `circle_polynomial_dissipative` | 对任意有限指标集和复系数，实际微分表达式的 L² 配对等于认证矩阵二次型并满足 `−21/4` 界；保留系数和周期识别条件 |
| 四阶表达式的 H² 能量形式 | `circle_classical_energy_eq`, `circle_multiply_pairing_integral` | 通过周期分部积分，将四阶项化为二阶导数的 L² 配对；系数乘法为真实有界算子，其配对等于 Haar 积分 |
| H² 近似中的一阶导数收敛 | `circle_first_derivative_norm_sq_le`, `circle_first_derivative_tendsto` | 证明 `‖f'‖² ≤ ‖f‖²+‖f''‖²`，因此函数及二阶弱导数收敛推出一阶弱导数收敛，不把后者作为额外假设 |
| 函数、前两阶导数同时近似 | `h2_circle_polynomial_tendsto`, `h2_circle_polynomial_first_tendsto`, `h2_circle_polynomial_second_tendsto` | 对所有 H² 加权余弦序列，有限多项式在三个实际 L² 分量中同时收敛；无需假设四阶导数存在 |
| 实际弱导数能量与系数形式 | `h2_circle_energy_eq_coefficients`, `circle_cosine_weak_energy_dissipative` | 利用能量连续性和已证明的近似，将实际 H² 形式识别为绝对收敛的系数二次型，并证明任意两次弱导数下的余弦扇区耗散 |
| 原稿曲率变量下的 H² 耗散 | `circle_h2_energy_profile`, `paper_cosine_weak_energy_dissipative` | 恢复原稿的 `153/4` 与 `45/4` 势能项；定理保留曲率 ODE、第一积分、Fourier 公式、反射对称及周期关系。具体 Jacobi 曲率满足这些条件及全文稳定性定理仍未完成 |
| 一阶反对称修正的实部消去 | `circle_multiply_l2_symmetric`, `circle_first_order_skew_energy` | 证明实连续系数乘法在 L² 中对称，且经典周期函数满足 `Re ⟨f,h f′+h′f/2⟩=0`；这不是无界算子伴随定义域的定理 |
| 原稿线性化表达式的实际能量 | `paper_linear_expression_split`, `paper_linear_classical_energy`, `paper_linear_classical_cosine_dissipative` | 核对 `−75qq′D`、`−69/2` 和 `−45q⁴/2` 的系数，用分部积分证明其实部能量等于已有 H² 形式；对属于余弦合成空间的经典函数取得条件耗散，仍待具体曲率识别和算子定义域论证 |
| L² 弱导数之间的分部积分和乘积规则 | `circle_weak_integration_by_parts`, `circle_real_multiply_weak_deriv`, `circle_weak_skew_energy` | 从全部 Fourier 乘子关系推出两组弱导数的分部积分，并对实 C¹ 系数证明弱乘积求导及反对称能量消去 |
| 四阶弱导数表达式的能量 | `circle_weak_symmetric_energy`, `circle_weak_linear_energy`, `circle_weak_linear_cosine_dissipative` | 用实际 L² 乘法定义四阶表达式，将四次逐次弱导数的实部配对识别为已有 H² 能量；未声称闭性、伴随定义域相等或全谱结论 |
| 显式 H⁴ 线性定义域 | `circle_h4_jet_unique`, `circle_h4_jet_add`, `circle_h4_jet_smul`, `circleH4Derivative` | 证明四次弱求导的函数构成复线性子空间，各阶导数唯一，故选择弱导数见证得到的映射是线性的 |
| 定义域上的四阶线性算子 | `circle_h4_operator_apply`, `circle_h4_operator_energy`, `circle_h4_operator_cosine_dissipative` | 真正定义 H⁴ 到 L² 的线性映射并证明实际内积能量与条件耗散；闭性和伴随定义域由后续正则性模块证明，紧预解算子和具体 Jacobi 系数识别仍未完成 |
| H⁴ 域上的形式伴随恒等式 | `circle_h4_symmetric_green`, `circle_weak_skew_green`, `circle_h4_formal_adjoint_green` | 对两个任意 H⁴ 函数证明实际 L² 配对恒等式，形式伴随为 `−4D⁴−45hD²−(105/2)h′D−42`；此结果只给出伴随关系的一侧包含，不能替代最大伴随定义域等于 H⁴ 的正则性证明 |
| H⁴ 定义域的稠密性 | `circle_fourier_mem_h4`, `circle_h4_domain_dense`, `circle_h4_pairing_separates` | 从经典 Fourier 模的各阶导数证明其属于 H⁴，再由 Fourier Hilbert 基的稠密张成得到整个 H⁴ 域在 L² 中稠密 |
| Mathlib 中的真正 Hilbert 伴随 | `circle_h4_formal_le_hilbert_adjoint`, `circle_h4_hilbert_adjoint_value`, `circle_h4_hilbert_adjoint_closed` | 将算子接到 Mathlib 的 `LinearPMap.adjoint`，证明形式伴随为其限制，并确认 H⁴ 上的值及伴随的闭性；反向域包含由下面的正则性证明补齐 |
| 原算子的可闭性 | `circle_h4_hilbert_adjoint_dense`, `circle_h4_pmap_closable` | 伴随域包含稠密的 H⁴ 域；反向 Green 配对又把原算子嵌入另一个闭伴随算子，从而证明可闭。可闭不等于给定 H⁴ 域上的原算子已经闭 |
| 最大伴随域的分布方程与 H² 提升 | `circle_hilbert_adjoint_fourier`, `circle_h2_of_fourth_distribution`, `circle_hilbert_adjoint_mem_h2` | 对任意伴随域元素测试全部 Fourier 模；由四阶主项和至多二阶的 L² 数据推出二阶乘子属于 ℓ²，不预设未知函数的弱导数 |
| 最大伴随域恰为 H⁴ | `circle_hilbert_adjoint_mem_h4`, `circle_hilbert_adjoint_domain`, `circle_hilbert_adjoint_eq_formal` | 对任意正周期和实 C² 系数，先获 H²，再由弱乘积公式构造第四阶 L² 导数及第三阶导数，证明真正 Hilbert 伴随等于论文给出的形式表达式；具体 Jacobi 曲率仍待识别 |
| 给定 H⁴ 定义域上的原算子闭性 | `circle_formal_adjoint_adjoint_eq`, `circle_h4_pmap_closed` | 对反向伴随也证明最大域正则性，得到 `B*=A`，再由 Hilbert 伴随的闭性证明原算子闭；未据此声称已有紧预解算子、扇形性或完整谱定理 |
| H⁴ 的完整 Fourier 刻画 | `circle_h4_iff_fourth_coefficients`, `circle_h4_of_fourth_fourier` | 原函数在 L² 且四阶乘子序列属于 ℓ² 当且仅当具有四次逐次 L² 弱导数；中间三阶导数由证明构造，不作为额外前提 |
| 四阶主项的正实参数预解算子 | `circle_principal_resolvent_norm_le`, `circle_principal_resolvent_mem_h4`, `circle_principal_resolvent_right_inverse`, `circle_principal_resolvent_left_inverse` | 在任意正周期上，对每个 λ>0 构造 L² 上有界逆，值域包含于实际 H⁴ 域，两侧逆等式都在该域上验证；尚未覆盖复参数角域的全部平滑估计 |
| 主项预解算子的紧性 | `circle_multiplier_hasSum_rank_one`, `circle_bounded_multiplier_compact`, `circle_principal_resolvent_compact` | 证明秩一展开按算子范数收敛，再以四次幂级数控制主项符号并单独处理零频；完整变系数算子的连接由下面的扰动构造补齐 |
| 主项逆的一、二阶弱导数估计 | `circle_principal_first_norm_le`, `circle_principal_second_norm_le`, `circle_principal_first_eq_jet`, `circle_principal_second_eq_jet` | 在 λ=p²、p≥1 时给出 5/(4p)、1/(4p) 的界，并与 H⁴ 输出的真实弱导数对应；这些粗界足以做扰动，不代表论文的全复角域最优幂次界 |
| 完整变系数算子的紧预解构造 | `circle_lower_resolvent_norm_lt_one`, `circle_full_shift_factorization`, `circle_full_compact_resolvent_exists` | 对任意连续复系数 h,h₁,h₂，在明确正参数构造 L² 上紧有界逆，值域在 H⁴，两侧逆等式均成立；没有预设低阶扰动小，参数由系数范数选择。Bloch 算子、有限秩修正、扇形性和全谱连接仍须证明 |
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
