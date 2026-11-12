import CentroidEscape.WeightedExpansion

/-!
# Rational certificates for the symmetric metric Jacobian

All identities below are elaborated and verified by Lean's kernel. The eight
positive sums of squares and sign congruences cover all 32 affine-box vertices.
No floating computation, external oracle, or native_decide is used.
-/
namespace CentroidEscape.MetricStability
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def metricSquare (h : Fin 7 → ℝ) : ℝ :=
  (h 0)^2+(h 1)^2+(h 2)^2+(h 3)^2+(h 4)^2+(h 5)^2+(h 6)^2

def boxForm (x y u w r : ℝ) (h : Fin 7 → ℝ) : ℝ :=
  (39/20)*metricSquare h -
    (h 0*h 2+h 1*h 3+h 0*h 6
    -(4/5)*w*h 2*h 4+(4/5)*u*h 3*h 4
    +(25/8-(12/25)*r)*h 4*h 5
    +(2/5)*w*h 0*h 5-(2/5)*u*h 1*h 5
    -(2/5)*y*h 2*h 5+(2/5)*x*h 3*h 5)

theorem base0 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (-(2092/7105:ℝ))*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (1468/7105:ℝ)*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (-(423785/548652:ℝ))*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (326429126141/519756328000:ℝ)*(h 5 + (-(109526195200/979287378423:ℝ))*h 6)^2 +
    (318058503124373/176271728116140:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base1 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (-(2092/7105:ℝ))*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (1468/7105:ℝ)*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (1513805/1645956:ℝ)*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (304025336423/1559268984000:ℝ)*(h 5 + (-(573672665600/912076009269:ℝ))*h 6)^2 +
    (94951777702373/54724560556140:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base2 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (236/1015:ℝ)*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (1468/7105:ℝ)*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (-(165667/182884:ℝ))*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (155080403453/519756328000:ℝ)*(h 5 + (752665600/155080403453:ℝ)*h 6)^2 +
    (151760980988309/83743417864620:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base3 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (236/1015:ℝ)*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (1468/7105:ℝ)*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (1294157/1645956:ℝ)*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (1013488815719/1559268984000:ℝ)*(h 5 + (-(238320089600/3040466447157:ℝ))*h 6)^2 +
    (329871303773669/182427986829420:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base4 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (-(2092/7105:ℝ))*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (-(1028/7105:ℝ))*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (-(1417787/1645956:ℝ))*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (647311098359/1559268984000:ℝ)*(h 5 + (-(315692569600/1941933295077:ℝ))*h 6)^2 +
    (209874408316309/116515997704620:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base5 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (-(2092/7105:ℝ))*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (-(1028/7105:ℝ))*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (455791/548652:ℝ)*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (262574051533/519756328000:ℝ)*(h 5 + (-(186928883200/787722154599:ℝ))*h 6)^2 +
    (252921068632549/141789987827820:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base6 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (236/1015:ℝ)*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (-(1028/7105:ℝ))*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (-(1637435/1645956:ℝ))*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (68937938423/1559268984000:ℝ)*(h 5 + (19660006400/206813815269:ℝ)*h 6)^2 +
    (22482581076373/12408828916140:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem base7 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h =
    (39/20:ℝ)*(h 0 + (-(10/39:ℝ))*h 2 + (-(22/195:ℝ))*h 5 + (-(10/39:ℝ))*h 6)^2 +
    (39/20:ℝ)*(h 1 + (-(10/39:ℝ))*h 3 + (22/195:ℝ)*h 5)^2 +
    (1421/780:ℝ)*(h 2 + (1716/7105:ℝ)*h 4 + (236/1015:ℝ)*h 5 + (-(100/1421:ℝ))*h 6)^2 +
    (1421/780:ℝ)*(h 3 + (-(1716/7105:ℝ))*h 4 + (-(1028/7105:ℝ))*h 5)^2 +
    (1234467/710500:ℝ)*(h 4 + (127525/182884:ℝ)*h 5 + (22000/1234467:ℝ)*h 6)^2 +
    (477619547341/519756328000:ℝ)*(h 5 + (-(25048230400/477619547341:ℝ))*h 6)^2 +
    (466746289599973/257914555564140:ℝ)*(h 6)^2 := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  positivity

theorem vertex0 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base6 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex1 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base7 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex2 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base4 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex3 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base5 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex4 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base2 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex5 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base3 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex6 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base0 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex7 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base1 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex8 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base4 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex9 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base5 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex10 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base6 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex11 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base7 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex12 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base0 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex13 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base1 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex14 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base2 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex15 (h : Fin 7 → ℝ) : 0 ≤ boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base3 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex16 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base2 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex17 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base3 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex18 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base0 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex19 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base1 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex20 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base6 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex21 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base7 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex22 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base4 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex23 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base5 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex24 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (0:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base0 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex25 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base1 ![-h 0,-h 1,-h 2,-h 3,h 4,h 5,-h 6]

theorem vertex26 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (0:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base2 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex27 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (-(11/10:ℝ)) (11/10:ℝ) (49/4:ℝ) h = boxForm (-(8/5:ℝ)) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base3 ![-h 0,h 1,-h 2,h 3,-h 4,-h 5,-h 6]

theorem vertex28 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (0:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base4 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex29 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (-(11/10:ℝ)) (49/4:ℝ) h = boxForm (8/5:ℝ) (-(12/5:ℝ)) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6] := by
    dsimp [boxForm, metricSquare]
    ring
  rw [he]
  exact base5 ![h 0,-h 1,h 2,-h 3,-h 4,-h 5,h 6]

theorem vertex30 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (0:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base6 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

theorem vertex31 (h : Fin 7 → ℝ) : 0 ≤ boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h := by
  have he : boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) h = boxForm (8/5:ℝ) (12/5:ℝ) (11/10:ℝ) (11/10:ℝ) (49/4:ℝ) ![h 0,h 1,h 2,h 3,h 4,h 5,h 6] := by
    rfl
  rw [he]
  exact base7 ![h 0,h 1,h 2,h 3,h 4,h 5,h 6]

end
end CentroidEscape.MetricStability

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape.MetricStability).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Metric certificate audit passed for {checked} declarations."
