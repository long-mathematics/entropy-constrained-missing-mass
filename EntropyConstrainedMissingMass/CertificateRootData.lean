import EntropyConstrainedMissingMass.CertificateLogData
import EntropyConstrainedMissingMass.CertificateRoots

/-! Every stored entropy root and objective bracket in Appendix D, checked in Lean. -/
namespace EntropyConstrainedMissingMass.Certificates
noncomputable section
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem index_0 : entropySupportIndex ((11 : ℝ)/10) = 3 := by
  have hl := log_bound_0
  have hu := log_bound_1
  norm_num only [div_one] at hl hu
  apply entropySupportIndex_eq_of_log_bounds (by norm_num)
  · norm_num only [Nat.cast_ofNat]
    linarith [hl.2]
  · norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith [hu.1]

theorem cutoff_0 : candidateCutoff 3 ((11 : ℝ)/10) = 5 := by
  unfold candidateCutoff
  have hc : ⌈(3 : ℝ)*((11 : ℝ)/10)+1⌉₊ = 5 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc ⊢
  rw [index_0, hc]
  norm_num

theorem entropy_sign_0_light_3_a : branchEntropy 3 ((160660804849263531983686271 : ℝ)/1000000000000000000000000000000) < ((11 : ℝ)/10) := by
  have hz := log_bound_2
  have hq := log_bound_3
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_0_light_3_b : ((11 : ℝ)/10) < branchEntropy 3 ((1255162537884871343622549 : ℝ)/7812500000000000000000000000) := by
  have hz := log_bound_4
  have hq := log_bound_5
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_0_light_3 : lightRoot ((11 : ℝ)/10) ∈ Ioo ((160660804849263531983686271 : ℝ)/1000000000000000000000000000000) ((1255162537884871343622549 : ℝ)/7812500000000000000000000000) := by
  apply lightRoot_mem_of_entropy_signs (by norm_num)
  · rw [index_0]; norm_num
  · rw [index_0]; norm_num
  · simpa only [index_0, Nat.cast_ofNat] using entropy_sign_0_light_3_a
  · simpa only [index_0, Nat.cast_ofNat] using entropy_sign_0_light_3_b

theorem value_0_light_3 : ((296480675541 : ℝ)/1000000000000) < lightValue 3 ((11 : ℝ)/10) ∧ lightValue 3 ((11 : ℝ)/10) < ((148240337771 : ℝ)/500000000000) := by
  have hr := root_0_light_3
  have hb := objective_certificate_nat 3 3 ((160660804849263531983686271 : ℝ)/1000000000000000000000000000000) (lightRoot ((11 : ℝ)/10)) ((1255162537884871343622549 : ℝ)/7812500000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  simp only [lightValue, index_0, Nat.cast_ofNat]
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_0_heavy_3_a : ((11 : ℝ)/10) < branchEntropy 3 ((304094389319567699388321409199 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_6
  have hq := log_bound_7
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_0_heavy_3_b : branchEntropy 3 ((608188778639135398776642818399 : ℝ)/1000000000000000000000000000000) < ((11 : ℝ)/10) := by
  have hz := log_bound_8
  have hq := log_bound_9
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_0_heavy_3 : heavyRoot ((11 : ℝ)/10) 3 ∈ Ioo ((304094389319567699388321409199 : ℝ)/500000000000000000000000000000) ((608188778639135398776642818399 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_0])
    (by norm_num) (by norm_num) entropy_sign_0_heavy_3_a entropy_sign_0_heavy_3_b

theorem value_0_heavy_3 : ((294054230107 : ℝ)/1000000000000) < heavyCandidateValue 3 ((11 : ℝ)/10) 3 ∧ heavyCandidateValue 3 ((11 : ℝ)/10) 3 < ((73513557527 : ℝ)/250000000000) := by
  have hr := root_0_heavy_3
  have hb := objective_certificate_nat 3 3 ((304094389319567699388321409199 : ℝ)/500000000000000000000000000000) (heavyRoot ((11 : ℝ)/10) 3) ((608188778639135398776642818399 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_0_heavy_4_a : ((11 : ℝ)/10) < branchEntropy 4 ((332999418081561548924500126651 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_10
  have hq := log_bound_11
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_0_heavy_4_b : branchEntropy 4 ((665998836163123097849000253303 : ℝ)/1000000000000000000000000000000) < ((11 : ℝ)/10) := by
  have hz := log_bound_12
  have hq := log_bound_13
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_0_heavy_4 : heavyRoot ((11 : ℝ)/10) 4 ∈ Ioo ((332999418081561548924500126651 : ℝ)/500000000000000000000000000000) ((665998836163123097849000253303 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_0])
    (by norm_num) (by norm_num) entropy_sign_0_heavy_4_a entropy_sign_0_heavy_4_b

theorem value_0_heavy_4 : ((1409702877 : ℝ)/5000000000) < heavyCandidateValue 3 ((11 : ℝ)/10) 4 ∧ heavyCandidateValue 3 ((11 : ℝ)/10) 4 < ((281940575401 : ℝ)/1000000000000) := by
  have hr := root_0_heavy_4
  have hb := objective_certificate_nat 4 3 ((332999418081561548924500126651 : ℝ)/500000000000000000000000000000) (heavyRoot ((11 : ℝ)/10) 4) ((665998836163123097849000253303 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_0_heavy_5_a : ((11 : ℝ)/10) < branchEntropy 5 ((139485491621143946293301924983 : ℝ)/200000000000000000000000000000) := by
  have hz := log_bound_14
  have hq := log_bound_15
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_0_heavy_5_b : branchEntropy 5 ((174356864526429932866627406229 : ℝ)/250000000000000000000000000000) < ((11 : ℝ)/10) := by
  have hz := log_bound_16
  have hq := log_bound_17
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_0_heavy_5 : heavyRoot ((11 : ℝ)/10) 5 ∈ Ioo ((139485491621143946293301924983 : ℝ)/200000000000000000000000000000) ((174356864526429932866627406229 : ℝ)/250000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_0])
    (by norm_num) (by norm_num) entropy_sign_0_heavy_5_a entropy_sign_0_heavy_5_b

theorem value_0_heavy_5 : ((67554650637 : ℝ)/250000000000) < heavyCandidateValue 3 ((11 : ℝ)/10) 5 ∧ heavyCandidateValue 3 ((11 : ℝ)/10) 5 < ((270218602549 : ℝ)/1000000000000) := by
  have hr := root_0_heavy_5
  have hb := objective_certificate_nat 5 3 ((139485491621143946293301924983 : ℝ)/200000000000000000000000000000) (heavyRoot ((11 : ℝ)/10) 5) ((174356864526429932866627406229 : ℝ)/250000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem index_1 : entropySupportIndex ((6 : ℝ)/5) = 3 := by
  have hl := log_bound_0
  have hu := log_bound_1
  norm_num only [div_one] at hl hu
  apply entropySupportIndex_eq_of_log_bounds (by norm_num)
  · norm_num only [Nat.cast_ofNat]
    linarith [hl.2]
  · norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith [hu.1]

theorem cutoff_1 : candidateCutoff 3 ((6 : ℝ)/5) = 5 := by
  unfold candidateCutoff
  have hc : ⌈(3 : ℝ)*((6 : ℝ)/5)+1⌉₊ = 5 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc ⊢
  rw [index_1, hc]
  norm_num

theorem entropy_sign_1_light_3_a : branchEntropy 3 ((3729200113262509028243254819 : ℝ)/125000000000000000000000000000) < ((6 : ℝ)/5) := by
  have hz := log_bound_18
  have hq := log_bound_19
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_1_light_3_b : ((6 : ℝ)/5) < branchEntropy 3 ((29833600906100072225946038553 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_20
  have hq := log_bound_21
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_1_light_3 : lightRoot ((6 : ℝ)/5) ∈ Ioo ((3729200113262509028243254819 : ℝ)/125000000000000000000000000000) ((29833600906100072225946038553 : ℝ)/1000000000000000000000000000000) := by
  apply lightRoot_mem_of_entropy_signs (by norm_num)
  · rw [index_1]; norm_num
  · rw [index_1]; norm_num
  · simpa only [index_1, Nat.cast_ofNat] using entropy_sign_1_light_3_a
  · simpa only [index_1, Nat.cast_ofNat] using entropy_sign_1_light_3_b

theorem value_1_light_3 : ((81938923013 : ℝ)/250000000000) < lightValue 3 ((6 : ℝ)/5) ∧ lightValue 3 ((6 : ℝ)/5) < ((327755692053 : ℝ)/1000000000000) := by
  have hr := root_1_light_3
  have hb := objective_certificate_nat 3 3 ((3729200113262509028243254819 : ℝ)/125000000000000000000000000000) (lightRoot ((6 : ℝ)/5)) ((29833600906100072225946038553 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  simp only [lightValue, index_1, Nat.cast_ofNat]
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_1_heavy_3_a : ((6 : ℝ)/5) < branchEntropy 3 ((536248550668522304908437585659 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_22
  have hq := log_bound_23
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_1_heavy_3_b : branchEntropy 3 ((26812427533426115245421879283 : ℝ)/50000000000000000000000000000) < ((6 : ℝ)/5) := by
  have hz := log_bound_24
  have hq := log_bound_25
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_1_heavy_3 : heavyRoot ((6 : ℝ)/5) 3 ∈ Ioo ((536248550668522304908437585659 : ℝ)/1000000000000000000000000000000) ((26812427533426115245421879283 : ℝ)/50000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_1])
    (by norm_num) (by norm_num) entropy_sign_1_heavy_3_a entropy_sign_1_heavy_3_b

theorem value_1_heavy_3 : ((166851179989 : ℝ)/500000000000) < heavyCandidateValue 3 ((6 : ℝ)/5) 3 ∧ heavyCandidateValue 3 ((6 : ℝ)/5) 3 < ((333702359979 : ℝ)/1000000000000) := by
  have hr := root_1_heavy_3
  have hb := objective_certificate_nat 3 3 ((536248550668522304908437585659 : ℝ)/1000000000000000000000000000000) (heavyRoot ((6 : ℝ)/5) 3) ((26812427533426115245421879283 : ℝ)/50000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_1_heavy_4_a : ((6 : ℝ)/5) < branchEntropy 4 ((307549121651151105920402001441 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_26
  have hq := log_bound_27
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_1_heavy_4_b : branchEntropy 4 ((615098243302302211840804002883 : ℝ)/1000000000000000000000000000000) < ((6 : ℝ)/5) := by
  have hz := log_bound_28
  have hq := log_bound_29
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_1_heavy_4 : heavyRoot ((6 : ℝ)/5) 4 ∈ Ioo ((307549121651151105920402001441 : ℝ)/500000000000000000000000000000) ((615098243302302211840804002883 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_1])
    (by norm_num) (by norm_num) entropy_sign_1_heavy_4_a entropy_sign_1_heavy_4_b

theorem value_1_heavy_4 : ((319213313159 : ℝ)/1000000000000) < heavyCandidateValue 3 ((6 : ℝ)/5) 4 ∧ heavyCandidateValue 3 ((6 : ℝ)/5) 4 < ((7980332829 : ℝ)/25000000000) := by
  have hr := root_1_heavy_4
  have hb := objective_certificate_nat 4 3 ((307549121651151105920402001441 : ℝ)/500000000000000000000000000000) (heavyRoot ((6 : ℝ)/5) 4) ((615098243302302211840804002883 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_1_heavy_5_a : ((6 : ℝ)/5) < branchEntropy 5 ((654801099196794560393206420059 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_30
  have hq := log_bound_31
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_1_heavy_5_b : branchEntropy 5 ((32740054959839728019660321003 : ℝ)/50000000000000000000000000000) < ((6 : ℝ)/5) := by
  have hz := log_bound_32
  have hq := log_bound_33
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_1_heavy_5 : heavyRoot ((6 : ℝ)/5) 5 ∈ Ioo ((654801099196794560393206420059 : ℝ)/1000000000000000000000000000000) ((32740054959839728019660321003 : ℝ)/50000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_1])
    (by norm_num) (by norm_num) entropy_sign_1_heavy_5_a entropy_sign_1_heavy_5_b

theorem value_1_heavy_5 : ((76364784193 : ℝ)/250000000000) < heavyCandidateValue 3 ((6 : ℝ)/5) 5 ∧ heavyCandidateValue 3 ((6 : ℝ)/5) 5 < ((305459136773 : ℝ)/1000000000000) := by
  have hr := root_1_heavy_5
  have hb := objective_certificate_nat 5 3 ((654801099196794560393206420059 : ℝ)/1000000000000000000000000000000) (heavyRoot ((6 : ℝ)/5) 5) ((32740054959839728019660321003 : ℝ)/50000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem index_2 : entropySupportIndex ((7 : ℝ)/5) = 4 := by
  have hl := log_bound_1
  have hu := log_bound_34
  norm_num only [div_one] at hl hu
  apply entropySupportIndex_eq_of_log_bounds (by norm_num)
  · norm_num only [Nat.cast_ofNat]
    linarith [hl.2]
  · norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith [hu.1]

theorem cutoff_2 : candidateCutoff 3 ((7 : ℝ)/5) = 6 := by
  unfold candidateCutoff
  have hc : ⌈(3 : ℝ)*((7 : ℝ)/5)+1⌉₊ = 6 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc ⊢
  rw [index_2, hc]
  norm_num

theorem entropy_sign_2_light_4_a : branchEntropy 4 ((2434107615234567484736411213 : ℝ)/1000000000000000000000000000000) < ((7 : ℝ)/5) := by
  have hz := log_bound_35
  have hq := log_bound_36
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_2_light_4_b : ((7 : ℝ)/5) < branchEntropy 4 ((1217053807617283742368205607 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_37
  have hq := log_bound_38
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_2_light_4 : lightRoot ((7 : ℝ)/5) ∈ Ioo ((2434107615234567484736411213 : ℝ)/1000000000000000000000000000000) ((1217053807617283742368205607 : ℝ)/500000000000000000000000000000) := by
  apply lightRoot_mem_of_entropy_signs (by norm_num)
  · rw [index_2]; norm_num
  · rw [index_2]; norm_num
  · simpa only [index_2, Nat.cast_ofNat] using entropy_sign_2_light_4_a
  · simpa only [index_2, Nat.cast_ofNat] using entropy_sign_2_light_4_b

theorem value_2_light_4 : ((42428970803 : ℝ)/100000000000) < lightValue 3 ((7 : ℝ)/5) ∧ lightValue 3 ((7 : ℝ)/5) < ((424289708031 : ℝ)/1000000000000) := by
  have hr := root_2_light_4
  have hb := objective_certificate_nat 4 3 ((2434107615234567484736411213 : ℝ)/1000000000000000000000000000000) (lightRoot ((7 : ℝ)/5)) ((1217053807617283742368205607 : ℝ)/500000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  simp only [lightValue, index_2, Nat.cast_ofNat]
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_2_heavy_4_a : ((7 : ℝ)/5) < branchEntropy 4 ((489968275298054639002161041831 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_39
  have hq := log_bound_40
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_2_heavy_4_b : branchEntropy 4 ((61246034412256829875270130229 : ℝ)/125000000000000000000000000000) < ((7 : ℝ)/5) := by
  have hz := log_bound_41
  have hq := log_bound_42
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_2_heavy_4 : heavyRoot ((7 : ℝ)/5) 4 ∈ Ioo ((489968275298054639002161041831 : ℝ)/1000000000000000000000000000000) ((61246034412256829875270130229 : ℝ)/125000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_2])
    (by norm_num) (by norm_num) entropy_sign_2_heavy_4_a entropy_sign_2_heavy_4_b

theorem value_2_heavy_4 : ((20187937233 : ℝ)/50000000000) < heavyCandidateValue 3 ((7 : ℝ)/5) 4 ∧ heavyCandidateValue 3 ((7 : ℝ)/5) 4 < ((403758744661 : ℝ)/1000000000000) := by
  have hr := root_2_heavy_4
  have hb := objective_certificate_nat 4 3 ((489968275298054639002161041831 : ℝ)/1000000000000000000000000000000) (heavyRoot ((7 : ℝ)/5) 4) ((61246034412256829875270130229 : ℝ)/125000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_2_heavy_5_a : ((7 : ℝ)/5) < branchEntropy 5 ((5567910933226195216721385481 : ℝ)/10000000000000000000000000000) := by
  have hz := log_bound_43
  have hq := log_bound_44
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_2_heavy_5_b : branchEntropy 5 ((556791093322619521672138548101 : ℝ)/1000000000000000000000000000000) < ((7 : ℝ)/5) := by
  have hz := log_bound_45
  have hq := log_bound_46
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_2_heavy_5 : heavyRoot ((7 : ℝ)/5) 5 ∈ Ioo ((5567910933226195216721385481 : ℝ)/10000000000000000000000000000) ((556791093322619521672138548101 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_2])
    (by norm_num) (by norm_num) entropy_sign_2_heavy_5_a entropy_sign_2_heavy_5_b

theorem value_2_heavy_5 : ((191981043271 : ℝ)/500000000000) < heavyCandidateValue 3 ((7 : ℝ)/5) 5 ∧ heavyCandidateValue 3 ((7 : ℝ)/5) 5 < ((383962086543 : ℝ)/1000000000000) := by
  have hr := root_2_heavy_5
  have hb := objective_certificate_nat 5 3 ((5567910933226195216721385481 : ℝ)/10000000000000000000000000000) (heavyRoot ((7 : ℝ)/5) 5) ((556791093322619521672138548101 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_2_heavy_6_a : ((7 : ℝ)/5) < branchEntropy 6 ((595298369198405264916788686747 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_47
  have hq := log_bound_48
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_2_heavy_6_b : branchEntropy 6 ((148824592299601316229197171687 : ℝ)/250000000000000000000000000000) < ((7 : ℝ)/5) := by
  have hz := log_bound_49
  have hq := log_bound_50
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_2_heavy_6 : heavyRoot ((7 : ℝ)/5) 6 ∈ Ioo ((595298369198405264916788686747 : ℝ)/1000000000000000000000000000000) ((148824592299601316229197171687 : ℝ)/250000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_2])
    (by norm_num) (by norm_num) entropy_sign_2_heavy_6_a entropy_sign_2_heavy_6_b

theorem value_2_heavy_6 : ((183833880733 : ℝ)/500000000000) < heavyCandidateValue 3 ((7 : ℝ)/5) 6 ∧ heavyCandidateValue 3 ((7 : ℝ)/5) 6 < ((367667761467 : ℝ)/1000000000000) := by
  have hr := root_2_heavy_6
  have hb := objective_certificate_nat 6 3 ((595298369198405264916788686747 : ℝ)/1000000000000000000000000000000) (heavyRoot ((7 : ℝ)/5) 6) ((148824592299601316229197171687 : ℝ)/250000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem index_3 : entropySupportIndex ((19 : ℝ)/8) = 10 := by
  have hl := log_bound_51
  have hu := log_bound_52
  norm_num only [div_one] at hl hu
  apply entropySupportIndex_eq_of_log_bounds (by norm_num)
  · norm_num only [Nat.cast_ofNat]
    linarith [hl.2]
  · norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith [hu.1]

theorem cutoff_3 : candidateCutoff 8 ((19 : ℝ)/8) = 20 := by
  unfold candidateCutoff
  have hc : ⌈(8 : ℝ)*((19 : ℝ)/8)+1⌉₊ = 20 :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc ⊢
  rw [index_3, hc]
  norm_num

theorem entropy_sign_3_light_10_a : branchEntropy 10 ((18148555030040734746124285599 : ℝ)/500000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_53
  have hq := log_bound_54
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_light_10_b : ((19 : ℝ)/8) < branchEntropy 10 ((36297110060081469492248571199 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_55
  have hq := log_bound_56
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_light_10 : lightRoot ((19 : ℝ)/8) ∈ Ioo ((18148555030040734746124285599 : ℝ)/500000000000000000000000000000) ((36297110060081469492248571199 : ℝ)/1000000000000000000000000000000) := by
  apply lightRoot_mem_of_entropy_signs (by norm_num)
  · rw [index_3]; norm_num
  · rw [index_3]; norm_num
  · simpa only [index_3, Nat.cast_ofNat] using entropy_sign_3_light_10_a
  · simpa only [index_3, Nat.cast_ofNat] using entropy_sign_3_light_10_b

theorem value_3_light_10 : ((91084161087 : ℝ)/200000000000) < lightValue 8 ((19 : ℝ)/8) ∧ lightValue 8 ((19 : ℝ)/8) < ((113855201359 : ℝ)/250000000000) := by
  have hr := root_3_light_10
  have hb := objective_certificate_nat 10 8 ((18148555030040734746124285599 : ℝ)/500000000000000000000000000000) (lightRoot ((19 : ℝ)/8)) ((36297110060081469492248571199 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  simp only [lightValue, index_3, Nat.cast_ofNat]
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_10_a : ((19 : ℝ)/8) < branchEntropy 10 ((15818273687470186523433696777 : ℝ)/100000000000000000000000000000) := by
  have hz := log_bound_57
  have hq := log_bound_58
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_10_b : branchEntropy 10 ((158182736874701865234336967771 : ℝ)/1000000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_59
  have hq := log_bound_60
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_10 : heavyRoot ((19 : ℝ)/8) 10 ∈ Ioo ((15818273687470186523433696777 : ℝ)/100000000000000000000000000000) ((158182736874701865234336967771 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_10_a entropy_sign_3_heavy_10_b

theorem value_3_heavy_10 : ((91293512463 : ℝ)/200000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 10 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 10 < ((114116890579 : ℝ)/250000000000) := by
  have hr := root_3_heavy_10
  have hb := objective_certificate_nat 10 8 ((15818273687470186523433696777 : ℝ)/100000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 10) ((158182736874701865234336967771 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_11_a : ((19 : ℝ)/8) < branchEntropy 11 ((238776297033637053215448658873 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_61
  have hq := log_bound_62
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_11_b : branchEntropy 11 ((119388148516818526607724329437 : ℝ)/500000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_63
  have hq := log_bound_64
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_11 : heavyRoot ((19 : ℝ)/8) 11 ∈ Ioo ((238776297033637053215448658873 : ℝ)/1000000000000000000000000000000) ((119388148516818526607724329437 : ℝ)/500000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_11_a entropy_sign_3_heavy_11_b

theorem value_3_heavy_11 : ((113955030989 : ℝ)/250000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 11 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 11 < ((455820123957 : ℝ)/1000000000000) := by
  have hr := root_3_heavy_11
  have hb := objective_certificate_nat 11 8 ((238776297033637053215448658873 : ℝ)/1000000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 11) ((119388148516818526607724329437 : ℝ)/500000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_12_a : ((19 : ℝ)/8) < branchEntropy 12 ((14228328664295696104766340261 : ℝ)/50000000000000000000000000000) := by
  have hz := log_bound_65
  have hq := log_bound_66
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_12_b : branchEntropy 12 ((284566573285913922095326805221 : ℝ)/1000000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_67
  have hq := log_bound_68
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_12 : heavyRoot ((19 : ℝ)/8) 12 ∈ Ioo ((14228328664295696104766340261 : ℝ)/50000000000000000000000000000) ((284566573285913922095326805221 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_12_a entropy_sign_3_heavy_12_b

theorem value_3_heavy_12 : ((457052010607 : ℝ)/1000000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 12 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 12 < ((28565750663 : ℝ)/62500000000) := by
  have hr := root_3_heavy_12
  have hb := objective_certificate_nat 12 8 ((14228328664295696104766340261 : ℝ)/50000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 12) ((284566573285913922095326805221 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_13_a : ((19 : ℝ)/8) < branchEntropy 13 ((63560941266480087912037530503 : ℝ)/200000000000000000000000000000) := by
  have hz := log_bound_69
  have hq := log_bound_70
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_13_b : branchEntropy 13 ((79451176583100109890046913129 : ℝ)/250000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_71
  have hq := log_bound_72
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_13 : heavyRoot ((19 : ℝ)/8) 13 ∈ Ioo ((63560941266480087912037530503 : ℝ)/200000000000000000000000000000) ((79451176583100109890046913129 : ℝ)/250000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_13_a entropy_sign_3_heavy_13_b

theorem value_3_heavy_13 : ((229068809271 : ℝ)/500000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 13 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 13 < ((458137618543 : ℝ)/1000000000000) := by
  have hr := root_3_heavy_13
  have hb := objective_certificate_nat 13 8 ((63560941266480087912037530503 : ℝ)/200000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 13) ((79451176583100109890046913129 : ℝ)/250000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_14_a : ((19 : ℝ)/8) < branchEntropy 14 ((171968566132426557940064792083 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_73
  have hq := log_bound_74
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_14_b : branchEntropy 14 ((343937132264853115880129584167 : ℝ)/1000000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_75
  have hq := log_bound_76
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_14 : heavyRoot ((19 : ℝ)/8) 14 ∈ Ioo ((171968566132426557940064792083 : ℝ)/500000000000000000000000000000) ((343937132264853115880129584167 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_14_a entropy_sign_3_heavy_14_b

theorem value_3_heavy_14 : ((28667911363 : ℝ)/62500000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 14 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 14 < ((458686581809 : ℝ)/1000000000000) := by
  have hr := root_3_heavy_14
  have hb := objective_certificate_nat 14 8 ((171968566132426557940064792083 : ℝ)/500000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 14) ((343937132264853115880129584167 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_15_a : ((19 : ℝ)/8) < branchEntropy 15 ((365395674565682433425720876949 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_77
  have hq := log_bound_78
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_15_b : branchEntropy 15 ((7307913491313648668514417539 : ℝ)/20000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_79
  have hq := log_bound_80
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_15 : heavyRoot ((19 : ℝ)/8) 15 ∈ Ioo ((365395674565682433425720876949 : ℝ)/1000000000000000000000000000000) ((7307913491313648668514417539 : ℝ)/20000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_15_a entropy_sign_3_heavy_15_b

theorem value_3_heavy_15 : ((458681062251 : ℝ)/1000000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 15 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 15 < ((114670265563 : ℝ)/250000000000) := by
  have hr := root_3_heavy_15
  have hb := objective_certificate_nat 15 8 ((365395674565682433425720876949 : ℝ)/1000000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 15) ((7307913491313648668514417539 : ℝ)/20000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_16_a : ((19 : ℝ)/8) < branchEntropy 16 ((191761428991267019258547705351 : ℝ)/500000000000000000000000000000) := by
  have hz := log_bound_81
  have hq := log_bound_82
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_16_b : branchEntropy 16 ((383522857982534038517095410703 : ℝ)/1000000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_83
  have hq := log_bound_84
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_16 : heavyRoot ((19 : ℝ)/8) 16 ∈ Ioo ((191761428991267019258547705351 : ℝ)/500000000000000000000000000000) ((383522857982534038517095410703 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_16_a entropy_sign_3_heavy_16_b

theorem value_3_heavy_16 : ((114549661781 : ℝ)/250000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 16 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 16 < ((3665589177 : ℝ)/8000000000) := by
  have hr := root_3_heavy_16
  have hb := objective_certificate_nat 16 8 ((191761428991267019258547705351 : ℝ)/500000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 16) ((383522857982534038517095410703 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_17_a : ((19 : ℝ)/8) < branchEntropy 17 ((399150723485684704025587702561 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_85
  have hq := log_bound_86
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_17_b : branchEntropy 17 ((199575361742842352012793851281 : ℝ)/500000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_87
  have hq := log_bound_88
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_17 : heavyRoot ((19 : ℝ)/8) 17 ∈ Ioo ((399150723485684704025587702561 : ℝ)/1000000000000000000000000000000) ((199575361742842352012793851281 : ℝ)/500000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_17_a entropy_sign_3_heavy_17_b

theorem value_3_heavy_17 : ((114333151571 : ℝ)/250000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 17 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 17 < ((91466521257 : ℝ)/200000000000) := by
  have hr := root_3_heavy_17
  have hb := objective_certificate_nat 17 8 ((399150723485684704025587702561 : ℝ)/1000000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 17) ((199575361742842352012793851281 : ℝ)/500000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_18_a : ((19 : ℝ)/8) < branchEntropy 18 ((25802160922198759322314436999 : ℝ)/62500000000000000000000000000) := by
  have hz := log_bound_89
  have hq := log_bound_90
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_18_b : branchEntropy 18 ((82566914951036029831406198397 : ℝ)/200000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_91
  have hq := log_bound_92
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_18 : heavyRoot ((19 : ℝ)/8) 18 ∈ Ioo ((25802160922198759322314436999 : ℝ)/62500000000000000000000000000) ((82566914951036029831406198397 : ℝ)/200000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_18_a entropy_sign_3_heavy_18_b

theorem value_3_heavy_18 : ((114042028371 : ℝ)/250000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 18 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 18 < ((91233622697 : ℝ)/200000000000) := by
  have hr := root_3_heavy_18
  have hb := objective_certificate_nat 18 8 ((25802160922198759322314436999 : ℝ)/62500000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 18) ((82566914951036029831406198397 : ℝ)/200000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_19_a : ((19 : ℝ)/8) < branchEntropy 19 ((106241202193565609535359521973 : ℝ)/250000000000000000000000000000) := by
  have hz := log_bound_93
  have hq := log_bound_94
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_19_b : branchEntropy 19 ((424964808774262438141438087893 : ℝ)/1000000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_95
  have hq := log_bound_96
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_19 : heavyRoot ((19 : ℝ)/8) 19 ∈ Ioo ((106241202193565609535359521973 : ℝ)/250000000000000000000000000000) ((424964808774262438141438087893 : ℝ)/1000000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_19_a entropy_sign_3_heavy_19_b

theorem value_3_heavy_19 : ((454776447419 : ℝ)/1000000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 19 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 19 < ((22738822371 : ℝ)/50000000000) := by
  have hr := root_3_heavy_19
  have hb := objective_certificate_nat 19 8 ((106241202193565609535359521973 : ℝ)/250000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 19) ((424964808774262438141438087893 : ℝ)/1000000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

theorem entropy_sign_3_heavy_20_a : ((19 : ℝ)/8) < branchEntropy 20 ((435826756675367683720690492011 : ℝ)/1000000000000000000000000000000) := by
  have hz := log_bound_97
  have hq := log_bound_98
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem entropy_sign_3_heavy_20_b : branchEntropy 20 ((108956689168841920930172623003 : ℝ)/250000000000000000000000000000) < ((19 : ℝ)/8) := by
  have hz := log_bound_99
  have hq := log_bound_100
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]

theorem root_3_heavy_20 : heavyRoot ((19 : ℝ)/8) 20 ∈ Ioo ((435826756675367683720690492011 : ℝ)/1000000000000000000000000000000) ((108956689168841920930172623003 : ℝ)/250000000000000000000000000000) := by
  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_3])
    (by norm_num) (by norm_num) entropy_sign_3_heavy_20_a entropy_sign_3_heavy_20_b

theorem value_3_heavy_20 : ((453215106693 : ℝ)/1000000000000) < heavyCandidateValue 8 ((19 : ℝ)/8) 20 ∧ heavyCandidateValue 8 ((19 : ℝ)/8) 20 < ((226607553347 : ℝ)/500000000000) := by
  have hr := root_3_heavy_20
  have hb := objective_certificate_nat 20 8 ((435826756675367683720690492011 : ℝ)/1000000000000000000000000000000) (heavyRoot ((19 : ℝ)/8) 20) ((108956689168841920930172623003 : ℝ)/250000000000000000000000000000)
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  unfold heavyCandidateValue
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)

end
end EntropyConstrainedMissingMass.Certificates
