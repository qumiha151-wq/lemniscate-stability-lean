import SolitonClassification.FrozenWitness
import SolitonClassification.FrozenChainCertificate

namespace ClosedSimilarity.FrozenStress.Endpoint
set_option maxRecDepth 250000
set_option maxHeartbeats 0

private def witnesses : List Row := frozenRows% [84,84,84,84,84,84,84,84,84,84,84,84,84,84,84,84]
  204737041721391112557085542461510966511681776208073766990478269086464150299458150887211563302220976208805377607130898087579597410067356067651835399544055 128417020665788267151342076090694450995415889149906524818091621197416546149435637372720571491668625965573633567064558520131461037695844568952444376140905 98235167740341718945425225778571825484346873065000582820262789793379068965538798248355890251348648242753254898819567872645105426620187271592471421820828 36360692466100023698874566502675096682423372536450075379603043135974766558282843471492080287602691191627956226152925611872060841295625545376645962680617

private def left : Mark := ⟨(-102368520860695556278542771230755483255840888104036883495239134543232075149729075443605781651110488104402688803565449043789798705033678033825917699772028),(-64208510332894133575671038045347225497707944574953262409045810598708273074717818686360285745834312982786816783532279260065730518847922284476222188070453),49117583870170859472712612889285912742173436532500291410131394896689534482769399124177945125674324121376627449409783936322552713310093635796235710910414,(-18180346233050011849437283251337548341211686268225037689801521567987383279141421735746040143801345595813978113076462805936030420647812772688322981340309)⟩
private def right : Mark := ⟨(-109520583327622701084494993662597310840185941783376463142985983990615206261463818291275619372835025359627137152832673418298263529302738727423256001793818),43140267920289761658575325294043970644837914743209301761536725484935047212227752499442139880353581318343907257451493640215510013080569679332834831384580,8401518755354957514994918119348073927106695933948265280623149438702558338267332040720753393434478031234537411827757439350420005259538839722266658214128,(-51696000976867284440713350390395828434804844811054889915758209538921909887222804770701457004267019460663476252442750557293946948772983675656167489866604)⟩

private theorem cell0 : Transports 80 81 left (startMark (rowAt witnesses 1)) :=
  checked_transport (rowAt witnesses 0) 80 _ _ (by decide) (by decide +kernel)

private theorem cell1 : Transports 81 82 (startMark (rowAt witnesses 1)) (startMark (rowAt witnesses 2)) :=
  checked_transport (rowAt witnesses 1) 81 _ _ (by decide) (by decide +kernel)

private theorem cell2 : Transports 82 83 (startMark (rowAt witnesses 2)) (startMark (rowAt witnesses 3)) :=
  checked_transport (rowAt witnesses 2) 82 _ _ (by decide) (by decide +kernel)

private theorem cell3 : Transports 83 84 (startMark (rowAt witnesses 3)) (startMark (rowAt witnesses 4)) :=
  checked_transport (rowAt witnesses 3) 83 _ _ (by decide) (by decide +kernel)

private theorem cell4 : Transports 84 85 (startMark (rowAt witnesses 4)) (startMark (rowAt witnesses 5)) :=
  checked_transport (rowAt witnesses 4) 84 _ _ (by decide) (by decide +kernel)

private theorem cell5 : Transports 85 86 (startMark (rowAt witnesses 5)) (startMark (rowAt witnesses 6)) :=
  checked_transport (rowAt witnesses 5) 85 _ _ (by decide) (by decide +kernel)

private theorem cell6 : Transports 86 87 (startMark (rowAt witnesses 6)) (startMark (rowAt witnesses 7)) :=
  checked_transport (rowAt witnesses 6) 86 _ _ (by decide) (by decide +kernel)

private theorem cell7 : Transports 87 88 (startMark (rowAt witnesses 7)) (startMark (rowAt witnesses 8)) :=
  checked_transport (rowAt witnesses 7) 87 _ _ (by decide) (by decide +kernel)

private theorem cell8 : Transports 88 89 (startMark (rowAt witnesses 8)) (startMark (rowAt witnesses 9)) :=
  checked_transport (rowAt witnesses 8) 88 _ _ (by decide) (by decide +kernel)

private theorem cell9 : Transports 89 90 (startMark (rowAt witnesses 9)) (startMark (rowAt witnesses 10)) :=
  checked_transport (rowAt witnesses 9) 89 _ _ (by decide) (by decide +kernel)

private theorem cell10 : Transports 90 91 (startMark (rowAt witnesses 10)) (startMark (rowAt witnesses 11)) :=
  checked_transport (rowAt witnesses 10) 90 _ _ (by decide) (by decide +kernel)

private theorem cell11 : Transports 91 92 (startMark (rowAt witnesses 11)) (startMark (rowAt witnesses 12)) :=
  checked_transport (rowAt witnesses 11) 91 _ _ (by decide) (by decide +kernel)

private theorem cell12 : Transports 92 93 (startMark (rowAt witnesses 12)) (startMark (rowAt witnesses 13)) :=
  checked_transport (rowAt witnesses 12) 92 _ _ (by decide) (by decide +kernel)

private theorem cell13 : Transports 93 94 (startMark (rowAt witnesses 13)) (startMark (rowAt witnesses 14)) :=
  checked_transport (rowAt witnesses 13) 93 _ _ (by decide) (by decide +kernel)

private theorem cell14 : Transports 94 95 (startMark (rowAt witnesses 14)) (startMark (rowAt witnesses 15)) :=
  checked_transport (rowAt witnesses 14) 94 _ _ (by decide) (by decide +kernel)

private theorem cell15 : Transports 95 96 (startMark (rowAt witnesses 15)) right :=
  checked_transport (rowAt witnesses 15) 95 _ _ (by decide) (by decide +kernel)

theorem positive_transport_80_96 : Transports 80 96 left right :=
  (((((((((((((((cell0.trans cell1).trans cell2).trans cell3).trans cell4).trans cell5).trans cell6).trans cell7).trans cell8).trans cell9).trans cell10).trans cell11).trans cell12).trans cell13).trans cell14).trans cell15)

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_transport_80_96
