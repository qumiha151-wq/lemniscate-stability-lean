# 论文与 Lean 对照表（未完成版）

当前依据是最新的 `audit/source/revised.tex`；每次修订后重新核对相应命题、量词及假设。
`original.tex` 仅供比较，不能把有限维或条件性结论误当成修订稿主定理。
下面的名称指代码中的陈述，是否编译成功以当前源文件哈希对应的 build.json 为准。

| 修订稿内容 | Lean 陈述 | 目前的对应边界 |
| --- | --- | --- |
| 第 2 节线性化常数与 Fourier 系数 | `linearization_zero_order`, `linearization_first_order`, `fourier_coefficient_identity` | 证明代数恒等式；变化公式本身尚未形式化 |
| 第 2 节旋转模 `A(qq_x)=0` | `rotation_kernel` | 对满足 ODE 和第一积分的实际可微函数证明；尚需把这些函数识别为几何 Bernoulli 曲率 |
| 带权行引理 | `weighted_row_dissipation`, `complex_weighted_row_dissipation` | 任意有限指标集的实或复二次型；余弦子空间的 Fourier 型表示及 H² 延拓见后续条件连接，其他子空间仍待处理 |
| 9 项余弦低频比较及其完整行意义 | `CoarseArithmetic.cosine_rows`, `cosine_low_rows_dissipative` | 从有理公式的内核计算，连接到系数公式定义的矩阵全行：前 20 项区间估计加全部加权尾项；矩阵与几何算子的识别仍待完成 |
| 区间算术 | `CoarseArithmetic.mul_sound`, `absUpper_sound`, `reciprocalPositive_sound`, `sqrt_enclosure_sound` | 已证明实数的四则、正倒数及平方根包络；整数外舍入还需补齐 |
| 几何级数尾公式 | `tail1_sound`, `tail2_sound`, `tail3_sound`, `hasSum_geometric_moment_four`, `hasSum_geometric_moment_five`, `hasSum_geometric_moment_six` | 以 `HasSum` 证明零至六阶矩和前三阶移位尾和的精确有理式；实际矩阵及约束项的控制还需逐项连接 |
| 正频 Fourier 系数包络 | `CoarseArithmetic.positive_fourier_enclosure` | 由参数有理界证明所有正整数频率的系数公式包络；Jacobi Fourier 展开仍需形式化 |
| 常数 Fourier 系数及无限尾项 | `CoarseArithmetic.summable_fourier_tail`, `fourier_tail_bound`, `constant_fourier_enclosure` | 证明整个系数级数收敛、任意正截断点的尾界及前四项加全尾的常数项包络；仍以参数有理界为假设 |
| 余弦矩阵条目的区间控制 | `CoarseArithmetic.cosine_matrix_enclosure` | 从收敛级数定义系数，逐项证明实矩阵公式被计算使用的区间包围；矩阵与几何微分算子的 Fourier 表示仍需识别 |
| `Q=exp(-π)` 的精确有理区间 | `CoarseArithmetic.refined_nome_bounds`, `CoarseArithmetic.Contains.mono` | 由已证明的圆周率二十位界和 26 项指数级数，得到宽度为 10⁻²¹ 的区间；删除独立的粗界定理，后续统一从这个区间取得所需界 |
| theta 级数的精确参数界 | `CoarseArithmetic.theta_enclosure`, `actual_nome_theta_r_bounds` | 仅用前三项及完整几何尾项，以分母 10²¹ 的端点控制 theta 级数及其负四次方；旧粗界证明已删除，所需粗常数由区间包含取得；与 `(π/(2K))²` 的椭圆积分恒等式尚待形式化 |
| 精确 Fourier 系数区间及向外舍入 | `refined_positive_fourier_enclosure`, `refined_constant_fourier_enclosure`, `roundInterval_sound` | 正频系数用单调性；常数项取前 40 项并控制完整无限尾项；向外舍入保留实数包含关系。具体残差的有限比较仍待 Lean 核验 |
| 参数界在矩阵中的实例化 | `CoarseArithmetic.theta_nome_cosine_matrix_enclosure` | 在 `Q=exp(-π)` 和 theta 参数下消除数值参数假设；不能据此宣称已证明矩阵就是原几何算子的表示 |
| 正弦约束中的 `ρ²<(87/500)²` | `CoarseArithmetic.sine_constraint_series_bound`, `theta_nome_sine_constraint_bound` | 控制全部 `j≥2` 的系数比平方级数并证明收敛；旋转系数的几何识别仍需形式化 |
| 正弦正交约束到首模估计 | `CoarseArithmetic.sine_constraint_first_mode`, `sine_constraint_mass_bound` | 已构造复系数 `ℓ²` 尾向量并应用 Cauchy–Schwarz；这里的正交条件仍以显式系数向量表述，几何旋转向量识别未完成 |
| 正弦条目及完整耦合行 | `theta_nome_sine_matrix_enclosure`, `sine_coupling_square_sum_bound`, `sine_coupling_norm_bound` | 对实际级数系数证明区间包含；前两个耦合项分别保留，其余项由二至六阶完整几何尾求和控制，证明平方和小于 3916、范数小于 63 |
| 正弦尾块的全部行与 H² 耗散 | `sine_all_tail_rows_dissipative`, `sine_tail_energy_summable`, `sine_tail_h2_form_dissipative` | 两个低行分别小于 −120、−1560，高行由实际四次多项式统一控制；所有行包含完整尾部，复二次型经绝对收敛延拓到 H² 系数域并满足 −100 界 |
| 正弦约束块形式的 −75 界 | `sine_h2_block_energy_bound`, `sine_h2_constrained_dissipative` | 块形式由实际首项、完整耦合 ℓ² 内积及完整尾块双级数定义；不再假设 −100 和 63 能量界。下述模块补齐其微分能量和旋转正交条件的连接，具体 Jacobi 实例化仍待完成 |
| 归一化正弦展开与首模分解 | `even_sine_orthonormal`, `circle_even_sine_norm_sq`, `circle_sine_block_inner`, `circle_sine_block_norm_sq` | 在实际周期 L² 中构造无限合成；尾部频率为 2(j+2)，与首模严格正交；未将该族视作整个 L² 的基 |
| 旋转方向的精确归一化 | `circle_rotation_norm_sq`, `circle_even_sine_parseval`, `circle_rotation_sine_mass` | 由 q′=p、p′=−q³ 和第一积分直接证明 ‖qp‖²=h₀/5；在偶频及反射对称的 Fourier 条件下，Parseval 给出正弦系数平方和 2h₀/(5r)，不使用额外的特殊函数积分公式 |
| 正弦 Fourier 系数与 H² 域 | `circle_even_sine_coeff_pos`, `circle_sine_mem_h2_iff`, `circle_sine_tail_mem_h2_iff`, `circle_sine_block_mem_h2_iff` | 完整识别全部频率；保留实际周期尺度并构造弱二阶导数，反向用 Fourier 抽样证明系数条件，没有仅证明单向包含 |
| 系数约束与实际 L² 正交 | `circle_sine_constraint_orthogonal_iff`, `circle_sine_sobolev_constrained_coefficient_energy` | 将已证明的 −75 系数形式界写成实际函数的 L² 质量和正交条件；尚不是微分能量恒等式 |
| 旋转方向 qq' 的条件识别 | `circle_sine_rotation_derivative`, `circle_sine_profile_rotation_orthogonal_iff`, `paper_sine_sobolev_constrained_coefficient_energy` | 对给定曲率导数及显式 Fourier 条件，证明约束向量与 qq' 相差非零标量；奇频为零单独列为前提。具体 Jacobi 函数满足这些条件仍须证明 |
| 正弦模的实际微分矩阵 | `circle_sine_jet_deriv`, `circle_sine_matrix_pairing`, `circle_sine_matrix_eq_coefficients` | 从经典导数和实际 L² 内积计算所有条目，核对正弦反射项的正号；系数 Fourier 公式及真实周期关系仍为显式前提 |
| 正弦首模与尾块的有限能量及极限 | `circle_sine_polynomial_h2_energy_eq_coefficients`, `sine_finite_block_form_tendsto` | 两条交叉项与共轭关系、完整耦合级数及尾块双级数均经证明，有限集合不限于固定截断 |
| 完整正弦 H² 微分能量 | `circle_sine_block_polynomial_first_tendsto`, `circle_sine_weak_energy_eq_coefficients`, `circle_sine_weak_energy_dissipative` | 函数与前两阶实际弱导数同时近似；因此系数形式等于真实微分能量，并得到 −75 约束耗散 |
| 原稿旋转正交条件下的正弦算子耗散 | `paper_sine_weak_energy_dissipative`, `paper_h4_operator_sine_dissipative` | 对实际 q q' 正交条件恢复曲率势能及 H⁴ 线性化算子上的 −75 界；具体 Jacobi 身份、其他子空间与全文结论仍待完成 |
| 完整正弦子空间的表示与耗散 | `circle_even_sine_sector_iff_representation`, `paper_h4_operator_even_sine_sector_dissipative` | 从实际 Fourier 系数构造首模和 ℓ² 尾序列，证明反对称且奇频为零的每个函数都被覆盖；算子估计没有附加的“存在系数表示”假设 |
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
| H² 近似中的一阶导数收敛 | `circle_weak_derivative_norm_sq_product`, `circle_first_derivative_tendsto` | 证明 `‖f'‖² ≤ ‖f‖·‖f''‖`，因此函数及二阶弱导数收敛推出一阶弱导数收敛，不把后者作为额外假设 |
| 函数、前两阶导数同时近似 | `h2_circle_polynomial_tendsto`, `h2_circle_polynomial_first_tendsto`, `h2_circle_polynomial_second_tendsto` | 对所有 H² 加权余弦序列，有限多项式在三个实际 L² 分量中同时收敛；无需假设四阶导数存在 |
| 实际弱导数能量与系数形式 | `h2_circle_energy_eq_coefficients`, `circle_cosine_weak_energy_dissipative` | 利用能量连续性和已证明的近似，将实际 H² 形式识别为绝对收敛的系数二次型，并证明任意两次弱导数下的余弦子空间耗散 |
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
| 完整变系数算子的紧预解构造 | `circle_lower_resolvent_norm_lt_one`, `circle_full_shift_factorization`, `circle_full_compact_resolvent_exists` | 对任意连续复系数 h,h₁,h₂，在明确正参数构造 L² 上紧有界逆，值域在 H⁴，两侧逆等式均成立；没有预设低阶扰动小，参数由系数范数选择。全谱连接由下一行补齐，Bloch 算子、有限秩修正和扇形性仍须证明 |
| 任意复参数的 Fredholm 二择一与全谱 | `circle_complex_shift_factorization`, `circle_complex_shift_alternative`, `circle_spectrum_iff_eigenvector` | 用已构造的紧逆分解任意 z−A，再应用 Mathlib 的紧算子 Fredholm 定理；谱按 H⁴ 域上的 L² 有界双侧逆定义，每个谱点均有非零 H⁴ 特征向量。具体谱隙仍依赖尚未完成的各子空间耗散和 Jacobi 参数识别 |
| 余弦偶频子空间的完备性 | `circle_even_cosine_sector_representation`, `circle_h4_operator_even_cosine_sector_dissipative` | 从任意满足反射对称且奇频为零的 L² 函数重建完整 ℓ² 余弦序列，单独处理常数模归一化；条件 −21/4 界覆盖整个子空间，无须另假设合成表示 |
| 反射与实际 H⁴ 算子的交换 | `circle_reflect_inner`, `circle_reflect_mem_h4`, `circle_h4_operator_reflect_of_even` | 由全部 Fourier 系数构造 L² 等距反射，证明保持 H⁴，各阶导数的符号以及连续系数乘法的反射恒等式；由 h 的反射对称和两次求导推出实际算子交换关系 |
| 完整偶频空间的正交拆分及耗散 | `circle_h4_operator_reflection_energy_split`, `circle_h4_operator_even_frequencies_dissipative`, `paper_h4_operator_even_frequencies_dissipative` | 任意仅含偶频且与旋转向量正交的 H⁴ 函数分成真实余弦、正弦两部分；交叉内积为零，合并 −21/4 与 −75 得到整个偶频空间的 −21/4 界。仍保留具体曲率 ODE、Fourier 数据及周期关系，不包含奇频/Bloch 子空间或全文定理 |
| Bernstein 展开与正性 | `degree_six_conversion`, `degree_four_conversion`, `odd_rows_positive_on_interval`, `OddArithmetic.odd_low_realEval_positive` | 已连接有理列表运算与真正实多项式求值，在整个 `[0,1/2]` 区间得到下界；与实际有限行及遗漏无穷和的对应关系见下 |
| 奇频正权重与绝对条目上界 | `OddArithmetic.odd_weight_positive`, `odd_weight_high_upper`, `theta_nome_odd_off_diagonal_bound` | 全参数区间上的权重正性、特殊低频权重和高频几何界；端点分支与逐项绝对值分支都被证明控制实际条目 |
| 奇频低频行证书的精确含义 | `OddArithmetic.odd_row_realEval_formula`, `odd_low_row_with_omitted_bound`, `odd_zero_row_with_omitted_bound` | 将十二个低行的证书连接到实际矩阵的有限部分加有理表达式 R_n；R_n 的实际无穷尾和含义由下面的模块补齐 |
| 奇频遗漏条目的几何界 | `OddArithmetic.odd_half_distance_abs`, `odd_matrix_off_tail_bound` | 使用真实整数半频距控制每个非对角项，保持参数 α∈[0,1/2] |
| 奇频低行的完整遗漏尾和 | `OddArithmetic.odd_omitted_tail_bound`, `odd_actual_omitted_le`, `odd_low_complete_head_tail_bound`, `odd_zero_complete_head_tail_bound` | 两侧 m=±(27+2k) 的无穷加权级数均收敛，和不超过原稿 R_n；与有限部分合并后取得十二个低行的界 |
| 完整整数索引的奇频低行耗散 | `OddArithmetic.odd_low_full_row_summable`, `odd_low_full_row_sum`, `odd_low_rows_dissipative`, `odd_zero_low_rows_dissipative` | 以频率 2k+1、k∈ℤ 表示全部奇频，证明完整行绝对可和以及分割求和等式；十二个低行归一化后在参数区间小于 −1，在零参数小于 −6 |
| 奇频高行的全部权重比 | `OddArithmetic.odd_signed_weight_envelope`, `odd_same_branch_weight_ratio`, `odd_cross_branch_weight_ratio` | 包含 ±1、±3、±5 例外列，同号比受 a^(k−j) 控制，异号比保留 37/16 因子；不假设权重逆有界 |
| 奇频高行的两侧无穷和 | `OddArithmetic.odd_same_branch_sum_bound`, `odd_cross_branch_sum_bound`, `odd_cross_constant_certificate` | 证明绝对收敛，按真实移位频率 v 求和；对每个 j≥6 证明异号贡献小于 8v²，常数比较由内核验证 |
| 奇频全部行与四次多项式 | `OddArithmetic.odd_high_row_quartic_bound`, `odd_high_rows_dissipative`, `odd_all_rows_dissipative`, `odd_zero_all_rows_dissipative` | 完整高频行受原稿四次式控制并小于 −3112；与低频行合并后，全部奇频行在 [0,1/2] 小于 −1，在零参数小于 −6 |
| 奇频有限复二次型耗散 | `OddArithmetic.odd_finite_form_dissipative`, `odd_zero_finite_form_dissipative` | 对任意有限整数指标集和任意复系数，系数矩阵的实二次型受 −1 或 −6 倍质量控制 |
| 奇频 H² 能量的绝对收敛 | `OddArithmetic.odd_sobolev_entry_bound`, `odd_sobolev_kernel_row_bound`, `odd_absolute_summable`, `odd_energy_summable` | 实际频率权重为 1+(2i+1)²，完整整数核行和不超过 512；由任意有限双和的统一界证明整个能量双级数绝对收敛 |
| 奇频无限 H² 系数形式的耗散 | `OddArithmetic.odd_energy_tendsto`, `odd_h2_form_dissipative`, `odd_zero_h2_form_dissipative` | 对每个 H² 加权复序列，在整个 [0,1/2] 上取得 −1 倍质量界，在零参数取得 −6 倍质量界 |
| 实际周期奇频空间的完整性与 H² 系数 | `circle_odd_fourier_hasSum`, `circle_odd_norm_sq`, `circle_odd_h2_coefficients` | 所有正负奇频重建函数并满足 Parseval；实际 H² 推出所需加权平方可和性，周期尺度关系显式保留 |
| 实际奇频 H² 能量与系数形式一致 | `circle_odd_polynomial_h2_energy_eq_coefficients`, `circle_odd_polynomial_second_tendsto`, `circle_odd_weak_energy_eq_coefficients` | 任意有限 Fourier 和的真实能量等式及函数、两阶导数同时收敛；由此识别整个无限形式 |
| 实际 H⁴ 算子的奇频耗散 | `circle_h4_operator_odd_dissipative`, `paper_h4_operator_odd_dissipative` | 对真实 H⁴ 域中每个奇频函数取得 −6‖f‖² 界；保留曲率 Fourier 与周期条件，非零参数 Bloch 识别仍待完成 |
| 实际奇偶频正交分解与算子交换 | `circle_frequency_parts_norm_sq`, `circle_even_frequency_part_mem_h4`, `circle_h4_operator_frequency_energy_split` | 投影保持实际 H⁴ 域并与算子交换，交叉能量消失；要求势函数的奇频系数为零，并从基展开证明乘法交换 |
| 单周期全空间的旋转正交补耗散 | `paper_h4_operator_rotation_complement_dissipative` | 对任意旋转正交的真实 H⁴ 函数证明 −21/4 界；所有频率均已覆盖，仍保留具体曲率数据和周期条件 |
| 零参数奇频矩阵的微分表达式含义 | `circle_odd_matrix_entry`, `circle_odd_mode_pairing`, `circle_odd_mode_off_bound` | 在明确 Fourier 数据和周期条件下，将矩阵识别为实际 L² 模配对；这里只处理 α=0，不包含非零参数的 Bloch 算子 |
| 84 项奇频及 12 项零参数比较 | `OddArithmetic.all_odd_bernstein_comparisons`, `all_odd_zero_comparisons` | 从完整有理公式计算；不能单独代表其无限尾界的分析意义 |
| 高频四次多项式方法 | `HighFrequency.cosine_high_bound`, `sine_high_bound`, `odd_high_bound`, `even_high_bound` | 已实例化四个实际多项式，内核从定义计算起点比较并证明所有阈值外实数上的上界；余弦、正弦及奇频实际行的连接已在对应模块完成，变换后偶频 Bloch 行仍待连接 |
| 旋转模属于真实定义域并被算子消去 | `circle_rotation_mem_h4`, `circle_rotation_h4_kernel` | 从曲率 ODE 显式构造 qq′ 的四阶弱导数，将其作为实际 H⁴ 域元素，再由第一积分证明已定义算子的值等于零；不是仅证明形式微分表达式的点态恒等式 |
| 实际单周期旋转核与广义核 | `paper_single_period_kernel`, `paper_single_period_no_generalized_kernel`, `paper_single_period_zero_mem_spectrum` | 已实例化实际算子，证明非零旋转向量张成核、没有非平凡二阶广义核链、零为谱点；具体 Jacobi Fourier 与周期数据仍显式保留 |
| 实际单周期完整谱界 | `paper_single_period_nonzero_spectral_bound` | 结合实际 H⁴ 算子的 Fredholm 选择定理，对每个非零谱点证明实部不超过 −21/4；尚未完成具体 Jacobi 实例与任意覆盖 Bloch 结论 |
| 精确归一化伴随零向量 | `circle_perturbed_inverse_of_kernel`, `NeutralCoerciveOperator.exists_unique_adjoint_neutral_of_inverse`, `paper_single_period_adjoint_vector` | 由 P−A 的真实有界逆构造唯一 ψ，证明其属于 H⁴ 且 A*ψ=0、⟨ψ,e⟩=1；未假定 Galerkin 向量为精确核，具体曲率数据和定量近似仍待完成 |
| 精确伴随零向量的对称性与实值性 | `paper_single_period_adjoint_vector_sector`, `paper_single_period_adjoint_real_sector`, `circle_real_sine_phase_fourier` | 由唯一性及反射、偶频投影、点态复共轭与实际算子的交换，推出 ψ 为实偶频正弦函数；共同乘 −i 后 Fourier 系数为实反对称序列且归一化内积保持 |
| 精确中性变换的可逆性与定义域 | `neutral_transform_right_inverse`, `neutral_transform_domain_left_inverse`, `paper_single_period_neutral_decomposition`, `circle_neutral_transform_reflect` | T 和 T⁻¹ 为真实 L² 有界映射，互逆并保持 H⁴；TAT⁻¹ 在该域上等于正交压缩，精确中性行列为零，T 与反射交换；具体 Jacobi 数据仍须实例化 |
| 实际 Householder 变换 | `circle_unit_rotation_phase_anchor`, `paper_rotation_householder_hypotheses`, `paper_householder_involutive`, `paper_householder_h4_involutive` | 首个反对称 Fourier 向量属于 H⁴ 且为单位向量；共同相位 −i 使旋转与它的配对严格为正，故分母大于 1；实际 U 保持内积、以自身为逆并保持 H⁴、偶频空间和反射对称 |
| 精确变换后的旋转零特征值对应的行列 | `circle_neutral_transform_common_phase`, `paper_exact_centered_neutral_exists` | T 在共同相位下不变；实际 UTA T⁻¹U 的固定 Fourier 基向量对应的列和行以及其对称配对均精确为零，未使用近似核。后续直接使用沿固定 Fourier 基向量的正交分解，无须显式构造 V |
| 实际 Bloch 四次多项式 | `circle_bloch_polynomial`, `circle_bloch_coefficient_reflect`, `circle_bloch_top_coefficient` | 在固定 H⁴ 域上展开 D+i(2π/T)α，证明每阶反射奇偶性和最高阶 −4r²I |
| 精确中性配对及参数因子消去 | `paper_centered_bloch_anchor_pairing`, `paper_centered_bloch_center_scaled`, `paper_centered_bloch_cross_row_scaled`, `paper_centered_bloch_cross_column_scaled` | 与固定 Fourier 基向量的内积等于精确 ⟨ψ,Aⱼe⟩；中性块恰有二次因子、正交交叉块恰有一次因子。明确在 α≠0 时除法，未把近似核代入；有限秩范数误差和统一负性仍待证明 |
| 非零参数 Fourier 矩阵 | `circle_bloch_basis_fourier`, `circle_bloch_odd_symmetric_pairing` | 从真实微分表达式计算任意 α∈ℝ 的矩阵；在实际 Fourier 和周期条件下，奇频对称配对等于已认证的参数矩阵 |
| 非零参数的完整奇频 H⁴ 耗散 | `circle_odd_polynomial_bloch_energy`, `circle_odd_bloch_energy_eq_coefficients`, `paper_h4_bloch_odd_dissipative` | 对每个 α∈[0,1/2]，经四阶导数同时逼近，将实际奇频算子能量识别为无限系数形式，得到 −‖f‖² 界；覆盖整个奇频 H⁴ 域，仍保留曲率 Fourier 和周期条件 |
| 伴随残差控制 L² 误差 | `circle_adjoint_residual_energy`, `paper_adjoint_trial_l2_error` | 对任意同归一化的偶频正弦 H⁴ 试探向量，真实 Green 恒等式与 −75 耗散给出 ‖ψ−t‖≤‖A*t‖/75；具体试探残差认证尚未完成 |
| 真实 Gårding 界与全部弱导数控制 | `paper_h4_operator_garding`, `paper_adjoint_all_derivative_bounds` | 第一积分、实系数乘法的平方配对及弱分部积分给出实际能量界；伴随方程再控制四阶导数 |
| H⁴ 伴随误差界 | `paper_adjoint_trial_h4_error` | 在角坐标导数和范数中得到 ≤177‖A*t‖；修订稿直接采用该强界及更短证明，最终稳定性结论未改变 |
| 固定有限 Fourier 试探函数的残差 | `circle_adjoint_polynomial_fourier`, `circle_adjoint_polynomial_norm_sq`, `circle_normalized_trial_pairing`, `circle_normalized_trial_adjoint_norm` | 用 Green 恒等式得到实际伴随算子的全部 Fourier 系数，Parseval 等式包含完整无限尾项；归一化仅需非零内积。最新文稿中具体有理系数的残差区间界仍待在 Lean 中认证 |
| 任意重数谱隙 | `multiple_cover_gap` | 仅有参数下界到平方谱隙的实数推论；Bloch 直和和谱隙阶数尚未形式化 |
| 加权局部理论 | `weighted_critical_exponents` | 仅验证三个指数等式；不是 PSW 存在唯一性定理 |
| 非线性正常稳定性 | 尚无完整 Lean 定理 | PSZ、最大正则性、平衡流形及平滑论证均有待形式化 |
| 曲率小量到 H2 正常图 | 尚无完整 Lean 定理 | 几何和 Sobolev 复合论证有待形式化 |
| 物理时间衰减换算 | `physical_decay_identity`, `normalizedTime_at_unit_scale` | 已证明指数衰减的精确幂次换算及等待时间下界；几何解的衰减尚未建立 |
| 主定理 1.1 | 尚无完整 Lean 定理 | 不得宣称已获 Lean 证明 |

最终核对还须检查：M 的整数和正性条件、旋转与平移的选择、重参数化的定向、
固定小邻域与逐阶定量小邻域的不同量化、物理时间起点、各常数依赖，以及
所有谱/算子定理使用的定义域。发现不一致时须修订论文并重新核查相关证明。
