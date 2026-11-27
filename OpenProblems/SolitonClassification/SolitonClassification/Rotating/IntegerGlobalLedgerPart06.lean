import SolitonClassification.Rotating.IntegerGlobalLedger

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
set_option maxHeartbeats 0
set_option maxRecDepth 20000


def fullLedger_0_0_2_0_0_0_0 : Tree := (.square Tree.short (.first (.axis 128 133 true) (.second Tree.short (.axis 130 134 true))) Tree.short)
theorem fullLedger_0_0_2_0_0_0_0_valid : check fullLedger_0_0_2_0_0_0_0 (-3001) (-2939) (-3001) (-2939)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_0_1 : Tree := (.second (.first (.axis 129 137 true) (.first (.axis 132 137 true) (.second Tree.short (.axis 134 138 false)))) (.first (.axis 129 141 false) (.axis 133 141 false)))
theorem fullLedger_0_0_2_0_0_0_1_valid : check fullLedger_0_0_2_0_0_0_1 (-3001) (-2939) (-2939) (-2876)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_0_2 : Tree := (.square Tree.short (.second (.first (.axis 136 140 false) Tree.short) (.axis 137 142 false)) Tree.short)
theorem fullLedger_0_0_2_0_0_0_2_valid : check fullLedger_0_0_2_0_0_0_2 (-2939) (-2876) (-2939) (-2876)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_0 : Tree := (.square fullLedger_0_0_2_0_0_0_0 fullLedger_0_0_2_0_0_0_1 fullLedger_0_0_2_0_0_0_2)
theorem fullLedger_0_0_2_0_0_0_valid : check fullLedger_0_0_2_0_0_0 (-3001) (-2876) (-3001) (-2876)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_0_0_0_valid,fullLedger_0_0_2_0_0_0_1_valid⟩,fullLedger_0_0_2_0_0_0_2_valid⟩⟩

def fullLedger_0_0_2_0_0_1_0 : Tree := (.second (.first (.axis 129 147 false) (.second (.axis 133 145 false) (.axis 133 149 false))) (.axis 131 155 false))
theorem fullLedger_0_0_2_0_0_1_0_valid : check fullLedger_0_0_2_0_0_1_0 (-3001) (-2939) (-2876) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_1_1 : Tree := (.second (.first (.axis 137 147 true) (.second (.first (.axis 140 145 true) (.second Tree.short (.axis 142 146 true))) (.axis 141 149 true))) (.first (.axis 137 155 false) (.axis 141 155 false)))
theorem fullLedger_0_0_2_0_0_1_1_valid : check fullLedger_0_0_2_0_0_1_1 (-2939) (-2876) (-2876) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_1 : Tree := (.first fullLedger_0_0_2_0_0_1_0 fullLedger_0_0_2_0_0_1_1)
theorem fullLedger_0_0_2_0_0_1_valid : check fullLedger_0_0_2_0_0_1 (-3001) (-2876) (-2876) (-2751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_0_1_0_valid,fullLedger_0_0_2_0_0_1_1_valid⟩

def fullLedger_0_0_2_0_0_2_0 : Tree := (.square Tree.short (.first (.axis 144 149 true) (.second Tree.short (.axis 146 150 true))) Tree.short)
theorem fullLedger_0_0_2_0_0_2_0_valid : check fullLedger_0_0_2_0_0_2_0 (-2876) (-2814) (-2876) (-2814)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_2_1 : Tree := (.second (.first (.axis 145 153 false) (.first (.axis 148 153 false) (.second Tree.short (.axis 150 154 false)))) (.first (.axis 145 157 false) (.axis 149 157 false)))
theorem fullLedger_0_0_2_0_0_2_1_valid : check fullLedger_0_0_2_0_0_2_1 (-2876) (-2814) (-2814) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_2_2 : Tree := (.square Tree.short (.second (.first (.axis 152 156 false) Tree.short) (.axis 153 158 true)) Tree.short)
theorem fullLedger_0_0_2_0_0_2_2_valid : check fullLedger_0_0_2_0_0_2_2 (-2814) (-2751) (-2814) (-2751)=true := by
  decide +kernel

def fullLedger_0_0_2_0_0_2 : Tree := (.square fullLedger_0_0_2_0_0_2_0 fullLedger_0_0_2_0_0_2_1 fullLedger_0_0_2_0_0_2_2)
theorem fullLedger_0_0_2_0_0_2_valid : check fullLedger_0_0_2_0_0_2 (-2876) (-2751) (-2876) (-2751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_0_2_0_valid,fullLedger_0_0_2_0_0_2_1_valid⟩,fullLedger_0_0_2_0_0_2_2_valid⟩⟩

def fullLedger_0_0_2_0_0 : Tree := (.square fullLedger_0_0_2_0_0_0 fullLedger_0_0_2_0_0_1 fullLedger_0_0_2_0_0_2)
theorem fullLedger_0_0_2_0_0_valid : check fullLedger_0_0_2_0_0 (-3001) (-2751) (-3001) (-2751)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_0_0_valid,fullLedger_0_0_2_0_0_1_valid⟩,fullLedger_0_0_2_0_0_2_valid⟩⟩

def fullLedger_0_0_2_0_1_0 : Tree := (.second (.axis 135 167 false) (.axis 135 183 false))
theorem fullLedger_0_0_2_0_1_0_valid : check fullLedger_0_0_2_0_1_0 (-3001) (-2876) (-2751) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_2_0_1_1_0_0 : Tree := (.second (.first (.axis 145 163 false) (.axis 149 163 false)) (.axis 147 171 false))
theorem fullLedger_0_0_2_0_1_1_0_0_valid : check fullLedger_0_0_2_0_1_1_0_0 (-2876) (-2814) (-2751) (-2626)=true := by
  decide +kernel

def fullLedger_0_0_2_0_1_1_0_1 : Tree := (.second (.first (.axis 153 163 true) (.second (.first (.axis 156 161 true) (.second Tree.short (.axis 158 162 true))) (.axis 157 165 true))) (.first (.axis 153 171 false) (.axis 157 171 false)))
theorem fullLedger_0_0_2_0_1_1_0_1_valid : check fullLedger_0_0_2_0_1_1_0_1 (-2814) (-2751) (-2751) (-2626)=true := by
  decide +kernel

def fullLedger_0_0_2_0_1_1_0 : Tree := (.first fullLedger_0_0_2_0_1_1_0_0 fullLedger_0_0_2_0_1_1_0_1)
theorem fullLedger_0_0_2_0_1_1_0_valid : check fullLedger_0_0_2_0_1_1_0 (-2876) (-2751) (-2751) (-2626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_1_1_0_0_valid,fullLedger_0_0_2_0_1_1_0_1_valid⟩

def fullLedger_0_0_2_0_1_1_1 : Tree := (.first (.axis 147 183 false) (.axis 155 183 false))
theorem fullLedger_0_0_2_0_1_1_1_valid : check fullLedger_0_0_2_0_1_1_1 (-2876) (-2751) (-2626) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_2_0_1_1 : Tree := (.second fullLedger_0_0_2_0_1_1_0 fullLedger_0_0_2_0_1_1_1)
theorem fullLedger_0_0_2_0_1_1_valid : check fullLedger_0_0_2_0_1_1 (-2876) (-2751) (-2751) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_1_1_0_valid,fullLedger_0_0_2_0_1_1_1_valid⟩

def fullLedger_0_0_2_0_1 : Tree := (.first fullLedger_0_0_2_0_1_0 fullLedger_0_0_2_0_1_1)
theorem fullLedger_0_0_2_0_1_valid : check fullLedger_0_0_2_0_1 (-3001) (-2751) (-2751) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_1_0_valid,fullLedger_0_0_2_0_1_1_valid⟩

def fullLedger_0_0_2_0_2_0_0 : Tree := (.square Tree.short (.first (.axis 160 165 true) (.second Tree.short (.axis 162 166 false))) Tree.short)
theorem fullLedger_0_0_2_0_2_0_0_valid : check fullLedger_0_0_2_0_2_0_0 (-2751) (-2689) (-2751) (-2689)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_0_1 : Tree := (.second (.first (.axis 161 169 false) (.first (.axis 164 169 false) (.second Tree.short (.axis 166 170 false)))) (.first (.axis 161 173 false) (.axis 165 173 true)))
theorem fullLedger_0_0_2_0_2_0_1_valid : check fullLedger_0_0_2_0_2_0_1 (-2751) (-2689) (-2689) (-2626)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_0_2 : Tree := (.square Tree.short (.second (.first (.axis 168 172 true) Tree.short) (.axis 169 174 true)) Tree.short)
theorem fullLedger_0_0_2_0_2_0_2_valid : check fullLedger_0_0_2_0_2_0_2 (-2689) (-2626) (-2689) (-2626)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_0 : Tree := (.square fullLedger_0_0_2_0_2_0_0 fullLedger_0_0_2_0_2_0_1 fullLedger_0_0_2_0_2_0_2)
theorem fullLedger_0_0_2_0_2_0_valid : check fullLedger_0_0_2_0_2_0 (-2751) (-2626) (-2751) (-2626)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_2_0_0_valid,fullLedger_0_0_2_0_2_0_1_valid⟩,fullLedger_0_0_2_0_2_0_2_valid⟩⟩

def fullLedger_0_0_2_0_2_1 : Tree := (.first (.second (.axis 163 179 false) (.axis 163 187 false)) (.second (.first (.axis 169 179 true) (.second (.first (.axis 172 177 true) (.second Tree.short (.axis 174 178 false))) (.axis 173 181 false))) (.first (.axis 169 187 false) (.axis 173 187 false))))
theorem fullLedger_0_0_2_0_2_1_valid : check fullLedger_0_0_2_0_2_1 (-2751) (-2626) (-2626) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_2_0 : Tree := (.square Tree.short (.first (.axis 176 181 false) (.second Tree.short (.axis 178 182 false))) Tree.short)
theorem fullLedger_0_0_2_0_2_2_0_valid : check fullLedger_0_0_2_0_2_2_0 (-2626) (-2564) (-2626) (-2564)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_2_1 : Tree := (.second (.first (.axis 177 185 false) (.first (.axis 180 185 true) (.second Tree.short (.axis 182 186 true)))) (.axis 179 189 true))
theorem fullLedger_0_0_2_0_2_2_1_valid : check fullLedger_0_0_2_0_2_2_1 (-2626) (-2564) (-2564) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_2_2 : Tree := (.square Tree.short (.second (.first (.axis 184 188 true) Tree.short) (.axis 185 190 true)) Tree.short)
theorem fullLedger_0_0_2_0_2_2_2_valid : check fullLedger_0_0_2_0_2_2_2 (-2564) (-2501) (-2564) (-2501)=true := by
  decide +kernel

def fullLedger_0_0_2_0_2_2 : Tree := (.square fullLedger_0_0_2_0_2_2_0 fullLedger_0_0_2_0_2_2_1 fullLedger_0_0_2_0_2_2_2)
theorem fullLedger_0_0_2_0_2_2_valid : check fullLedger_0_0_2_0_2_2 (-2626) (-2501) (-2626) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_2_2_0_valid,fullLedger_0_0_2_0_2_2_1_valid⟩,fullLedger_0_0_2_0_2_2_2_valid⟩⟩

def fullLedger_0_0_2_0_2 : Tree := (.square fullLedger_0_0_2_0_2_0 fullLedger_0_0_2_0_2_1 fullLedger_0_0_2_0_2_2)
theorem fullLedger_0_0_2_0_2_valid : check fullLedger_0_0_2_0_2 (-2751) (-2501) (-2751) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_2_0_valid,fullLedger_0_0_2_0_2_1_valid⟩,fullLedger_0_0_2_0_2_2_valid⟩⟩

def fullLedger_0_0_2_0 : Tree := (.square fullLedger_0_0_2_0_0 fullLedger_0_0_2_0_1 fullLedger_0_0_2_0_2)
theorem fullLedger_0_0_2_0_valid : check fullLedger_0_0_2_0 (-3001) (-2501) (-3001) (-2501)=true := by
  exact Bool.and_eq_true_iff.mpr ⟨by decide,Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨fullLedger_0_0_2_0_0_valid,fullLedger_0_0_2_0_1_valid⟩,fullLedger_0_0_2_0_2_valid⟩⟩


end SolitonClassification.Rotating.IntegerTarget.GlobalCount
