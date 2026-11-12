import SolitonClassification.Rotating.FirstResidualIntegerData60
namespace SolitonClassification.Rotating.FirstResidualInteger60
open Candidate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false


private theorem extendBound (P : ℕ → Prop) (n : ℕ)
    (h : ∀i<n,P i) (hn : P n) : ∀i<n+1,P i := by
  intro i hi
  by_cases hlt : i<n
  · exact h i hlt
  · have he : i=n := by omega
    simpa only [he] using hn


theorem squareRank0 : squareDataValue squares 0=fixedTaylorNextSquare mesh 0 BenchState60.table := by decide +kernel

theorem squareRank1 : squareDataValue squares 1=fixedTaylorNextSquare mesh 1 BenchState60.table := by decide +kernel

theorem squareRank2 : squareDataValue squares 2=fixedTaylorNextSquare mesh 2 BenchState60.table := by decide +kernel

theorem squareRank3 : squareDataValue squares 3=fixedTaylorNextSquare mesh 3 BenchState60.table := by decide +kernel

theorem squareRank4 : squareDataValue squares 4=fixedTaylorNextSquare mesh 4 BenchState60.table := by decide +kernel

theorem squareRank5 : squareDataValue squares 5=fixedTaylorNextSquare mesh 5 BenchState60.table := by decide +kernel

theorem squareRank6 : squareDataValue squares 6=fixedTaylorNextSquare mesh 6 BenchState60.table := by decide +kernel

theorem squareRank7 : squareDataValue squares 7=fixedTaylorNextSquare mesh 7 BenchState60.table := by decide +kernel

theorem squareRank8 : squareDataValue squares 8=fixedTaylorNextSquare mesh 8 BenchState60.table := by decide +kernel

theorem squareRank9 : squareDataValue squares 9=fixedTaylorNextSquare mesh 9 BenchState60.table := by decide +kernel

theorem squareRank10 : squareDataValue squares 10=fixedTaylorNextSquare mesh 10 BenchState60.table := by decide +kernel

theorem squareRank11 : squareDataValue squares 11=fixedTaylorNextSquare mesh 11 BenchState60.table := by decide +kernel

theorem squareRank12 : squareDataValue squares 12=fixedTaylorNextSquare mesh 12 BenchState60.table := by decide +kernel

theorem squareRank13 : squareDataValue squares 13=fixedTaylorNextSquare mesh 13 BenchState60.table := by decide +kernel

theorem squareRank14 : squareDataValue squares 14=fixedTaylorNextSquare mesh 14 BenchState60.table := by decide +kernel

theorem squareRank15 : squareDataValue squares 15=fixedTaylorNextSquare mesh 15 BenchState60.table := by decide +kernel

theorem squareRank16 : squareDataValue squares 16=fixedTaylorNextSquare mesh 16 BenchState60.table := by decide +kernel

theorem squareRank17 : squareDataValue squares 17=fixedTaylorNextSquare mesh 17 BenchState60.table := by decide +kernel

theorem squareRank18 : squareDataValue squares 18=fixedTaylorNextSquare mesh 18 BenchState60.table := by decide +kernel

theorem squareRank19 : squareDataValue squares 19=fixedTaylorNextSquare mesh 19 BenchState60.table := by decide +kernel

theorem squareRank20 : squareDataValue squares 20=fixedTaylorNextSquare mesh 20 BenchState60.table := by decide +kernel

theorem squareRank21 : squareDataValue squares 21=fixedTaylorNextSquare mesh 21 BenchState60.table := by decide +kernel

theorem squareRank22 : squareDataValue squares 22=fixedTaylorNextSquare mesh 22 BenchState60.table := by decide +kernel

theorem squareRank23 : squareDataValue squares 23=fixedTaylorNextSquare mesh 23 BenchState60.table := by decide +kernel

theorem squareRank24 : squareDataValue squares 24=fixedTaylorNextSquare mesh 24 BenchState60.table := by decide +kernel

theorem squareRank25 : squareDataValue squares 25=fixedTaylorNextSquare mesh 25 BenchState60.table := by decide +kernel

theorem squareRank26 : squareDataValue squares 26=fixedTaylorNextSquare mesh 26 BenchState60.table := by decide +kernel

theorem squareRank27 : squareDataValue squares 27=fixedTaylorNextSquare mesh 27 BenchState60.table := by decide +kernel

theorem squareRank28 : squareDataValue squares 28=fixedTaylorNextSquare mesh 28 BenchState60.table := by decide +kernel

theorem squareRank29 : squareDataValue squares 29=fixedTaylorNextSquare mesh 29 BenchState60.table := by decide +kernel

theorem squareRank30 : squareDataValue squares 30=fixedTaylorNextSquare mesh 30 BenchState60.table := by decide +kernel

theorem squareRank31 : squareDataValue squares 31=fixedTaylorNextSquare mesh 31 BenchState60.table := by decide +kernel

theorem squareRank32 : squareDataValue squares 32=fixedTaylorNextSquare mesh 32 BenchState60.table := by decide +kernel

theorem squareRank33 : squareDataValue squares 33=fixedTaylorNextSquare mesh 33 BenchState60.table := by decide +kernel

theorem squareRank34 : squareDataValue squares 34=fixedTaylorNextSquare mesh 34 BenchState60.table := by decide +kernel

theorem squareRank35 : squareDataValue squares 35=fixedTaylorNextSquare mesh 35 BenchState60.table := by decide +kernel

theorem squareRank36 : squareDataValue squares 36=fixedTaylorNextSquare mesh 36 BenchState60.table := by decide +kernel

theorem squareRank37 : squareDataValue squares 37=fixedTaylorNextSquare mesh 37 BenchState60.table := by decide +kernel

theorem squareRank38 : squareDataValue squares 38=fixedTaylorNextSquare mesh 38 BenchState60.table := by decide +kernel

theorem squareRank39 : squareDataValue squares 39=fixedTaylorNextSquare mesh 39 BenchState60.table := by decide +kernel

theorem squareRank40 : squareDataValue squares 40=fixedTaylorNextSquare mesh 40 BenchState60.table := by decide +kernel

theorem squareRank41 : squareDataValue squares 41=fixedTaylorNextSquare mesh 41 BenchState60.table := by decide +kernel

theorem squareRank42 : squareDataValue squares 42=fixedTaylorNextSquare mesh 42 BenchState60.table := by decide +kernel

theorem squareRank43 : squareDataValue squares 43=fixedTaylorNextSquare mesh 43 BenchState60.table := by decide +kernel

theorem squareRank44 : squareDataValue squares 44=fixedTaylorNextSquare mesh 44 BenchState60.table := by decide +kernel

theorem squareRank45 : squareDataValue squares 45=fixedTaylorNextSquare mesh 45 BenchState60.table := by decide +kernel

theorem squareRank46 : squareDataValue squares 46=fixedTaylorNextSquare mesh 46 BenchState60.table := by decide +kernel

theorem squareRank47 : squareDataValue squares 47=fixedTaylorNextSquare mesh 47 BenchState60.table := by decide +kernel

theorem squareRank48 : squareDataValue squares 48=fixedTaylorNextSquare mesh 48 BenchState60.table := by decide +kernel

theorem squareRank49 : squareDataValue squares 49=fixedTaylorNextSquare mesh 49 BenchState60.table := by decide +kernel

theorem squareRank50 : squareDataValue squares 50=fixedTaylorNextSquare mesh 50 BenchState60.table := by decide +kernel

theorem squareRank51 : squareDataValue squares 51=fixedTaylorNextSquare mesh 51 BenchState60.table := by decide +kernel

theorem squareRank52 : squareDataValue squares 52=fixedTaylorNextSquare mesh 52 BenchState60.table := by decide +kernel

theorem squareRank53 : squareDataValue squares 53=fixedTaylorNextSquare mesh 53 BenchState60.table := by decide +kernel

theorem squareRank54 : squareDataValue squares 54=fixedTaylorNextSquare mesh 54 BenchState60.table := by decide +kernel

theorem squareRank55 : squareDataValue squares 55=fixedTaylorNextSquare mesh 55 BenchState60.table := by decide +kernel

theorem squareRank56 : squareDataValue squares 56=fixedTaylorNextSquare mesh 56 BenchState60.table := by decide +kernel

theorem squareRank57 : squareDataValue squares 57=fixedTaylorNextSquare mesh 57 BenchState60.table := by decide +kernel

theorem squareRank58 : squareDataValue squares 58=fixedTaylorNextSquare mesh 58 BenchState60.table := by decide +kernel

theorem squareRank59 : squareDataValue squares 59=fixedTaylorNextSquare mesh 59 BenchState60.table := by decide +kernel

theorem squareRank60 : squareDataValue squares 60=fixedTaylorNextSquare mesh 60 BenchState60.table := by decide +kernel

theorem squareRank61 : squareDataValue squares 61=fixedTaylorNextSquare mesh 61 BenchState60.table := by decide +kernel

theorem squareRank62 : squareDataValue squares 62=fixedTaylorNextSquare mesh 62 BenchState60.table := by decide +kernel

theorem squareRank63 : squareDataValue squares 63=fixedTaylorNextSquare mesh 63 BenchState60.table := by decide +kernel

theorem squareRank64 : squareDataValue squares 64=fixedTaylorNextSquare mesh 64 BenchState60.table := by decide +kernel

theorem squareRank65 : squareDataValue squares 65=fixedTaylorNextSquare mesh 65 BenchState60.table := by decide +kernel

theorem squareRank66 : squareDataValue squares 66=fixedTaylorNextSquare mesh 66 BenchState60.table := by decide +kernel

theorem squareRank67 : squareDataValue squares 67=fixedTaylorNextSquare mesh 67 BenchState60.table := by decide +kernel

theorem squareRank68 : squareDataValue squares 68=fixedTaylorNextSquare mesh 68 BenchState60.table := by decide +kernel

theorem squareRank69 : squareDataValue squares 69=fixedTaylorNextSquare mesh 69 BenchState60.table := by decide +kernel

theorem squareRank70 : squareDataValue squares 70=fixedTaylorNextSquare mesh 70 BenchState60.table := by decide +kernel

theorem squareRank71 : squareDataValue squares 71=fixedTaylorNextSquare mesh 71 BenchState60.table := by decide +kernel

theorem squareRank72 : squareDataValue squares 72=fixedTaylorNextSquare mesh 72 BenchState60.table := by decide +kernel

theorem squareRank73 : squareDataValue squares 73=fixedTaylorNextSquare mesh 73 BenchState60.table := by decide +kernel

theorem squareRank74 : squareDataValue squares 74=fixedTaylorNextSquare mesh 74 BenchState60.table := by decide +kernel

theorem squareRank75 : squareDataValue squares 75=fixedTaylorNextSquare mesh 75 BenchState60.table := by decide +kernel

theorem squareRank76 : squareDataValue squares 76=fixedTaylorNextSquare mesh 76 BenchState60.table := by decide +kernel

theorem squareRank77 : squareDataValue squares 77=fixedTaylorNextSquare mesh 77 BenchState60.table := by decide +kernel

theorem squareRank78 : squareDataValue squares 78=fixedTaylorNextSquare mesh 78 BenchState60.table := by decide +kernel

theorem squareRank79 : squareDataValue squares 79=fixedTaylorNextSquare mesh 79 BenchState60.table := by decide +kernel

theorem squareRank80 : squareDataValue squares 80=fixedTaylorNextSquare mesh 80 BenchState60.table := by decide +kernel

theorem squareRank81 : squareDataValue squares 81=fixedTaylorNextSquare mesh 81 BenchState60.table := by decide +kernel

theorem squareRank82 : squareDataValue squares 82=fixedTaylorNextSquare mesh 82 BenchState60.table := by decide +kernel

theorem squareRank83 : squareDataValue squares 83=fixedTaylorNextSquare mesh 83 BenchState60.table := by decide +kernel

theorem squareRank84 : squareDataValue squares 84=fixedTaylorNextSquare mesh 84 BenchState60.table := by decide +kernel

theorem squareRank85 : squareDataValue squares 85=fixedTaylorNextSquare mesh 85 BenchState60.table := by decide +kernel

theorem squareRank86 : squareDataValue squares 86=fixedTaylorNextSquare mesh 86 BenchState60.table := by decide +kernel

theorem squareRank87 : squareDataValue squares 87=fixedTaylorNextSquare mesh 87 BenchState60.table := by decide +kernel

theorem squareRank88 : squareDataValue squares 88=fixedTaylorNextSquare mesh 88 BenchState60.table := by decide +kernel

theorem squareRank89 : squareDataValue squares 89=fixedTaylorNextSquare mesh 89 BenchState60.table := by decide +kernel

theorem squareRank90 : squareDataValue squares 90=fixedTaylorNextSquare mesh 90 BenchState60.table := by decide +kernel

theorem squareRank91 : squareDataValue squares 91=fixedTaylorNextSquare mesh 91 BenchState60.table := by decide +kernel

theorem squareRank92 : squareDataValue squares 92=fixedTaylorNextSquare mesh 92 BenchState60.table := by decide +kernel

theorem squareRank93 : squareDataValue squares 93=fixedTaylorNextSquare mesh 93 BenchState60.table := by decide +kernel

theorem squareRank94 : squareDataValue squares 94=fixedTaylorNextSquare mesh 94 BenchState60.table := by decide +kernel

theorem squareRank95 : squareDataValue squares 95=fixedTaylorNextSquare mesh 95 BenchState60.table := by decide +kernel

theorem squareRank96 : squareDataValue squares 96=fixedTaylorNextSquare mesh 96 BenchState60.table := by decide +kernel

theorem squareRank97 : squareDataValue squares 97=fixedTaylorNextSquare mesh 97 BenchState60.table := by decide +kernel

theorem squareRank98 : squareDataValue squares 98=fixedTaylorNextSquare mesh 98 BenchState60.table := by decide +kernel

theorem squareRank99 : squareDataValue squares 99=fixedTaylorNextSquare mesh 99 BenchState60.table := by decide +kernel

theorem squareRank100 : squareDataValue squares 100=fixedTaylorNextSquare mesh 100 BenchState60.table := by decide +kernel

theorem squareRank101 : squareDataValue squares 101=fixedTaylorNextSquare mesh 101 BenchState60.table := by decide +kernel

theorem squareRank102 : squareDataValue squares 102=fixedTaylorNextSquare mesh 102 BenchState60.table := by decide +kernel

theorem squareRank103 : squareDataValue squares 103=fixedTaylorNextSquare mesh 103 BenchState60.table := by decide +kernel

theorem squareRank104 : squareDataValue squares 104=fixedTaylorNextSquare mesh 104 BenchState60.table := by decide +kernel

theorem squareRank105 : squareDataValue squares 105=fixedTaylorNextSquare mesh 105 BenchState60.table := by decide +kernel

theorem squareRank106 : squareDataValue squares 106=fixedTaylorNextSquare mesh 106 BenchState60.table := by decide +kernel

theorem squareRank107 : squareDataValue squares 107=fixedTaylorNextSquare mesh 107 BenchState60.table := by decide +kernel

theorem squareRank108 : squareDataValue squares 108=fixedTaylorNextSquare mesh 108 BenchState60.table := by decide +kernel

theorem squareRank109 : squareDataValue squares 109=fixedTaylorNextSquare mesh 109 BenchState60.table := by decide +kernel

theorem squareRank110 : squareDataValue squares 110=fixedTaylorNextSquare mesh 110 BenchState60.table := by decide +kernel

theorem squareRank111 : squareDataValue squares 111=fixedTaylorNextSquare mesh 111 BenchState60.table := by decide +kernel

theorem squareRank112 : squareDataValue squares 112=fixedTaylorNextSquare mesh 112 BenchState60.table := by decide +kernel

theorem squareRank113 : squareDataValue squares 113=fixedTaylorNextSquare mesh 113 BenchState60.table := by decide +kernel

theorem squareRank114 : squareDataValue squares 114=fixedTaylorNextSquare mesh 114 BenchState60.table := by decide +kernel

theorem squareRank115 : squareDataValue squares 115=fixedTaylorNextSquare mesh 115 BenchState60.table := by decide +kernel

theorem squareRank116 : squareDataValue squares 116=fixedTaylorNextSquare mesh 116 BenchState60.table := by decide +kernel

theorem squareRank117 : squareDataValue squares 117=fixedTaylorNextSquare mesh 117 BenchState60.table := by decide +kernel

theorem squareRank118 : squareDataValue squares 118=fixedTaylorNextSquare mesh 118 BenchState60.table := by decide +kernel

theorem squareRank119 : squareDataValue squares 119=fixedTaylorNextSquare mesh 119 BenchState60.table := by decide +kernel

theorem squareRank120 : squareDataValue squares 120=fixedTaylorNextSquare mesh 120 BenchState60.table := by decide +kernel

theorem squareRank121 : squareDataValue squares 121=fixedTaylorNextSquare mesh 121 BenchState60.table := by decide +kernel

theorem squareRank122 : squareDataValue squares 122=fixedTaylorNextSquare mesh 122 BenchState60.table := by decide +kernel

theorem squareRank123 : squareDataValue squares 123=fixedTaylorNextSquare mesh 123 BenchState60.table := by decide +kernel

theorem squareRank124 : squareDataValue squares 124=fixedTaylorNextSquare mesh 124 BenchState60.table := by decide +kernel

theorem squareRank125 : squareDataValue squares 125=fixedTaylorNextSquare mesh 125 BenchState60.table := by decide +kernel

theorem squareRank126 : squareDataValue squares 126=fixedTaylorNextSquare mesh 126 BenchState60.table := by decide +kernel

theorem squareRank127 : squareDataValue squares 127=fixedTaylorNextSquare mesh 127 BenchState60.table := by decide +kernel

theorem squareRank128 : squareDataValue squares 128=fixedTaylorNextSquare mesh 128 BenchState60.table := by decide +kernel

theorem squareRank129 : squareDataValue squares 129=fixedTaylorNextSquare mesh 129 BenchState60.table := by decide +kernel

theorem squareRank130 : squareDataValue squares 130=fixedTaylorNextSquare mesh 130 BenchState60.table := by decide +kernel

theorem squareRank131 : squareDataValue squares 131=fixedTaylorNextSquare mesh 131 BenchState60.table := by decide +kernel

theorem squareRank132 : squareDataValue squares 132=fixedTaylorNextSquare mesh 132 BenchState60.table := by decide +kernel

theorem squareRank133 : squareDataValue squares 133=fixedTaylorNextSquare mesh 133 BenchState60.table := by decide +kernel

theorem squareRank134 : squareDataValue squares 134=fixedTaylorNextSquare mesh 134 BenchState60.table := by decide +kernel

theorem squareRank135 : squareDataValue squares 135=fixedTaylorNextSquare mesh 135 BenchState60.table := by decide +kernel

theorem squareRank136 : squareDataValue squares 136=fixedTaylorNextSquare mesh 136 BenchState60.table := by decide +kernel

theorem squareRank137 : squareDataValue squares 137=fixedTaylorNextSquare mesh 137 BenchState60.table := by decide +kernel

theorem squareRank138 : squareDataValue squares 138=fixedTaylorNextSquare mesh 138 BenchState60.table := by decide +kernel

theorem squareRank139 : squareDataValue squares 139=fixedTaylorNextSquare mesh 139 BenchState60.table := by decide +kernel

theorem squareRank140 : squareDataValue squares 140=fixedTaylorNextSquare mesh 140 BenchState60.table := by decide +kernel

theorem squareRank141 : squareDataValue squares 141=fixedTaylorNextSquare mesh 141 BenchState60.table := by decide +kernel

theorem squareRank142 : squareDataValue squares 142=fixedTaylorNextSquare mesh 142 BenchState60.table := by decide +kernel

theorem squareRank143 : squareDataValue squares 143=fixedTaylorNextSquare mesh 143 BenchState60.table := by decide +kernel

theorem squareRank144 : squareDataValue squares 144=fixedTaylorNextSquare mesh 144 BenchState60.table := by decide +kernel

theorem squareRank145 : squareDataValue squares 145=fixedTaylorNextSquare mesh 145 BenchState60.table := by decide +kernel

theorem squareRank146 : squareDataValue squares 146=fixedTaylorNextSquare mesh 146 BenchState60.table := by decide +kernel

theorem squareRank147 : squareDataValue squares 147=fixedTaylorNextSquare mesh 147 BenchState60.table := by decide +kernel

theorem squareRank148 : squareDataValue squares 148=fixedTaylorNextSquare mesh 148 BenchState60.table := by decide +kernel

theorem squareRank149 : squareDataValue squares 149=fixedTaylorNextSquare mesh 149 BenchState60.table := by decide +kernel

theorem squareRank150 : squareDataValue squares 150=fixedTaylorNextSquare mesh 150 BenchState60.table := by decide +kernel

theorem squareRank151 : squareDataValue squares 151=fixedTaylorNextSquare mesh 151 BenchState60.table := by decide +kernel

theorem squareRank152 : squareDataValue squares 152=fixedTaylorNextSquare mesh 152 BenchState60.table := by decide +kernel

theorem squareRank153 : squareDataValue squares 153=fixedTaylorNextSquare mesh 153 BenchState60.table := by decide +kernel

theorem squareRank154 : squareDataValue squares 154=fixedTaylorNextSquare mesh 154 BenchState60.table := by decide +kernel

theorem squareRank155 : squareDataValue squares 155=fixedTaylorNextSquare mesh 155 BenchState60.table := by decide +kernel

theorem squareRank156 : squareDataValue squares 156=fixedTaylorNextSquare mesh 156 BenchState60.table := by decide +kernel

theorem squareRank157 : squareDataValue squares 157=fixedTaylorNextSquare mesh 157 BenchState60.table := by decide +kernel

theorem squareRank158 : squareDataValue squares 158=fixedTaylorNextSquare mesh 158 BenchState60.table := by decide +kernel

theorem squareRank159 : squareDataValue squares 159=fixedTaylorNextSquare mesh 159 BenchState60.table := by decide +kernel

theorem squareRank160 : squareDataValue squares 160=fixedTaylorNextSquare mesh 160 BenchState60.table := by decide +kernel

theorem squareRank161 : squareDataValue squares 161=fixedTaylorNextSquare mesh 161 BenchState60.table := by decide +kernel

theorem squareRank162 : squareDataValue squares 162=fixedTaylorNextSquare mesh 162 BenchState60.table := by decide +kernel

theorem squareRank163 : squareDataValue squares 163=fixedTaylorNextSquare mesh 163 BenchState60.table := by decide +kernel

theorem squareRank164 : squareDataValue squares 164=fixedTaylorNextSquare mesh 164 BenchState60.table := by decide +kernel

theorem squareRank165 : squareDataValue squares 165=fixedTaylorNextSquare mesh 165 BenchState60.table := by decide +kernel

theorem squareRank166 : squareDataValue squares 166=fixedTaylorNextSquare mesh 166 BenchState60.table := by decide +kernel

theorem squareRank167 : squareDataValue squares 167=fixedTaylorNextSquare mesh 167 BenchState60.table := by decide +kernel

theorem squareRank168 : squareDataValue squares 168=fixedTaylorNextSquare mesh 168 BenchState60.table := by decide +kernel

theorem squareRank169 : squareDataValue squares 169=fixedTaylorNextSquare mesh 169 BenchState60.table := by decide +kernel

theorem squareRank170 : squareDataValue squares 170=fixedTaylorNextSquare mesh 170 BenchState60.table := by decide +kernel

theorem squareRank171 : squareDataValue squares 171=fixedTaylorNextSquare mesh 171 BenchState60.table := by decide +kernel

theorem squareRank172 : squareDataValue squares 172=fixedTaylorNextSquare mesh 172 BenchState60.table := by decide +kernel

theorem squareRank173 : squareDataValue squares 173=fixedTaylorNextSquare mesh 173 BenchState60.table := by decide +kernel

theorem squareRank174 : squareDataValue squares 174=fixedTaylorNextSquare mesh 174 BenchState60.table := by decide +kernel

theorem squareRank175 : squareDataValue squares 175=fixedTaylorNextSquare mesh 175 BenchState60.table := by decide +kernel

theorem squareRank176 : squareDataValue squares 176=fixedTaylorNextSquare mesh 176 BenchState60.table := by decide +kernel

theorem squareRank177 : squareDataValue squares 177=fixedTaylorNextSquare mesh 177 BenchState60.table := by decide +kernel

theorem squareRank178 : squareDataValue squares 178=fixedTaylorNextSquare mesh 178 BenchState60.table := by decide +kernel

theorem squareRank179 : squareDataValue squares 179=fixedTaylorNextSquare mesh 179 BenchState60.table := by decide +kernel

theorem squareRank180 : squareDataValue squares 180=fixedTaylorNextSquare mesh 180 BenchState60.table := by decide +kernel

theorem squares_checked : ExtendedSquareValid mesh 180 BenchState60.table squares := by
  let P : ℕ → Prop := fun n=>squareDataValue squares n=fixedTaylorNextSquare mesh n BenchState60.table
  have hall : ∀n<181,P n := (extendBound P 180 (extendBound P 179 (extendBound P 178 (extendBound P 177 (extendBound P 176 (extendBound P 175 (extendBound P 174 (extendBound P 173 (extendBound P 172 (extendBound P 171 (extendBound P 170 (extendBound P 169 (extendBound P 168 (extendBound P 167 (extendBound P 166 (extendBound P 165 (extendBound P 164 (extendBound P 163 (extendBound P 162 (extendBound P 161 (extendBound P 160 (extendBound P 159 (extendBound P 158 (extendBound P 157 (extendBound P 156 (extendBound P 155 (extendBound P 154 (extendBound P 153 (extendBound P 152 (extendBound P 151 (extendBound P 150 (extendBound P 149 (extendBound P 148 (extendBound P 147 (extendBound P 146 (extendBound P 145 (extendBound P 144 (extendBound P 143 (extendBound P 142 (extendBound P 141 (extendBound P 140 (extendBound P 139 (extendBound P 138 (extendBound P 137 (extendBound P 136 (extendBound P 135 (extendBound P 134 (extendBound P 133 (extendBound P 132 (extendBound P 131 (extendBound P 130 (extendBound P 129 (extendBound P 128 (extendBound P 127 (extendBound P 126 (extendBound P 125 (extendBound P 124 (extendBound P 123 (extendBound P 122 (extendBound P 121 (extendBound P 120 (extendBound P 119 (extendBound P 118 (extendBound P 117 (extendBound P 116 (extendBound P 115 (extendBound P 114 (extendBound P 113 (extendBound P 112 (extendBound P 111 (extendBound P 110 (extendBound P 109 (extendBound P 108 (extendBound P 107 (extendBound P 106 (extendBound P 105 (extendBound P 104 (extendBound P 103 (extendBound P 102 (extendBound P 101 (extendBound P 100 (extendBound P 99 (extendBound P 98 (extendBound P 97 (extendBound P 96 (extendBound P 95 (extendBound P 94 (extendBound P 93 (extendBound P 92 (extendBound P 91 (extendBound P 90 (extendBound P 89 (extendBound P 88 (extendBound P 87 (extendBound P 86 (extendBound P 85 (extendBound P 84 (extendBound P 83 (extendBound P 82 (extendBound P 81 (extendBound P 80 (extendBound P 79 (extendBound P 78 (extendBound P 77 (extendBound P 76 (extendBound P 75 (extendBound P 74 (extendBound P 73 (extendBound P 72 (extendBound P 71 (extendBound P 70 (extendBound P 69 (extendBound P 68 (extendBound P 67 (extendBound P 66 (extendBound P 65 (extendBound P 64 (extendBound P 63 (extendBound P 62 (extendBound P 61 (extendBound P 60 (extendBound P 59 (extendBound P 58 (extendBound P 57 (extendBound P 56 (extendBound P 55 (extendBound P 54 (extendBound P 53 (extendBound P 52 (extendBound P 51 (extendBound P 50 (extendBound P 49 (extendBound P 48 (extendBound P 47 (extendBound P 46 (extendBound P 45 (extendBound P 44 (extendBound P 43 (extendBound P 42 (extendBound P 41 (extendBound P 40 (extendBound P 39 (extendBound P 38 (extendBound P 37 (extendBound P 36 (extendBound P 35 (extendBound P 34 (extendBound P 33 (extendBound P 32 (extendBound P 31 (extendBound P 30 (extendBound P 29 (extendBound P 28 (extendBound P 27 (extendBound P 26 (extendBound P 25 (extendBound P 24 (extendBound P 23 (extendBound P 22 (extendBound P 21 (extendBound P 20 (extendBound P 19 (extendBound P 18 (extendBound P 17 (extendBound P 16 (extendBound P 15 (extendBound P 14 (extendBound P 13 (extendBound P 12 (extendBound P 11 (extendBound P 10 (extendBound P 9 (extendBound P 8 (extendBound P 7 (extendBound P 6 (extendBound P 5 (extendBound P 4 (extendBound P 3 (extendBound P 2 (extendBound P 1 (extendBound P 0 (fun i hi => (Nat.not_lt_zero i hi).elim) squareRank0) squareRank1) squareRank2) squareRank3) squareRank4) squareRank5) squareRank6) squareRank7) squareRank8) squareRank9) squareRank10) squareRank11) squareRank12) squareRank13) squareRank14) squareRank15) squareRank16) squareRank17) squareRank18) squareRank19) squareRank20) squareRank21) squareRank22) squareRank23) squareRank24) squareRank25) squareRank26) squareRank27) squareRank28) squareRank29) squareRank30) squareRank31) squareRank32) squareRank33) squareRank34) squareRank35) squareRank36) squareRank37) squareRank38) squareRank39) squareRank40) squareRank41) squareRank42) squareRank43) squareRank44) squareRank45) squareRank46) squareRank47) squareRank48) squareRank49) squareRank50) squareRank51) squareRank52) squareRank53) squareRank54) squareRank55) squareRank56) squareRank57) squareRank58) squareRank59) squareRank60) squareRank61) squareRank62) squareRank63) squareRank64) squareRank65) squareRank66) squareRank67) squareRank68) squareRank69) squareRank70) squareRank71) squareRank72) squareRank73) squareRank74) squareRank75) squareRank76) squareRank77) squareRank78) squareRank79) squareRank80) squareRank81) squareRank82) squareRank83) squareRank84) squareRank85) squareRank86) squareRank87) squareRank88) squareRank89) squareRank90) squareRank91) squareRank92) squareRank93) squareRank94) squareRank95) squareRank96) squareRank97) squareRank98) squareRank99) squareRank100) squareRank101) squareRank102) squareRank103) squareRank104) squareRank105) squareRank106) squareRank107) squareRank108) squareRank109) squareRank110) squareRank111) squareRank112) squareRank113) squareRank114) squareRank115) squareRank116) squareRank117) squareRank118) squareRank119) squareRank120) squareRank121) squareRank122) squareRank123) squareRank124) squareRank125) squareRank126) squareRank127) squareRank128) squareRank129) squareRank130) squareRank131) squareRank132) squareRank133) squareRank134) squareRank135) squareRank136) squareRank137) squareRank138) squareRank139) squareRank140) squareRank141) squareRank142) squareRank143) squareRank144) squareRank145) squareRank146) squareRank147) squareRank148) squareRank149) squareRank150) squareRank151) squareRank152) squareRank153) squareRank154) squareRank155) squareRank156) squareRank157) squareRank158) squareRank159) squareRank160) squareRank161) squareRank162) squareRank163) squareRank164) squareRank165) squareRank166) squareRank167) squareRank168) squareRank169) squareRank170) squareRank171) squareRank172) squareRank173) squareRank174) squareRank175) squareRank176) squareRank177) squareRank178) squareRank179) squareRank180)
  intro n
  exact hall n.val n.isLt


end SolitonClassification.Rotating.FirstResidualInteger60
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
  logInfo "Integer residual extended-square ranks audit passed."
