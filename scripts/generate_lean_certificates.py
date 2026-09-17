#!/usr/bin/env python3
"""Generate explicit kernel-checked rational proofs from Appendix D's stored data.

Python supplies only rational terms and Lean proof scripts. No native_decide or
external oracle is used: Lean checks every arithmetic and analytic step.
"""
from pathlib import Path
from fractions import Fraction as Q
import missing_mass_extremizers_certificates as C

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'EntropyConstrainedMissingMass'

def rr(x):
    x = Q(x)
    return f'(({x.numerator} : ℝ)/{x.denominator})'

def rounded(lo, hi, digits):
    sc = 10 ** digits
    return Q(lo.numerator * sc // lo.denominator, sc), Q(-((-hi.numerator * sc) // hi.denominator), sc)

values = {}
def add_log(x):
    x=Q(x)
    if x not in values: values[x] = f'log_bound_{len(values)}'
    return values[x]
for hs,t,k,M,rows,winner in C.CASES:
    add_log(k);add_log(k+1)
    for branch,m,num in rows:
        for z in (Q(num,C.DEN), Q(num+1,C.DEN)):
            add_log(z);add_log((1-z)/m)

s = '''import EntropyConstrainedMissingMass.LogCertificateData

/-! Generated exact rational logarithm enclosures for Appendix D.
Regenerate with scripts/generate_lean_certificates.py; all arithmetic is kernel-checked. -/
namespace EntropyConstrainedMissingMass.Certificates
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
l2,u2=rounded(*C.log_bounds(Q(2)),38)
for x,name in values.items():
    y=x;j=0
    while y<1:y*=2;j-=1
    while y>=2:y/=2;j+=1
    ly,uy=rounded(*C.log_bounds(y),38)
    if j>=0:lo,hi=ly+j*l2,uy+j*u2
    else:lo,hi=ly+j*u2,uy+j*l2
    lo,hi=rounded(lo,hi,36)
    hy_proof = '    norm_num\n' if y == 1 else f'''    have h := log_certificate_normalized (y := {rr(y)}) (by norm_num) 40
    norm_num [logSeries, logRemainder, Finset.sum_range_succ] at h
    constructor <;> linarith [h.1,h.2]
'''
    s+=f'''
theorem {name} : {rr(lo)} ≤ Real.log {rr(x)} ∧ Real.log {rr(x)} ≤ {rr(hi)} := by
  have hy : {rr(ly)} ≤ Real.log {rr(y)} ∧ Real.log {rr(y)} ≤ {rr(uy)} := by
{hy_proof}  have he := log_range_reduction (x := {rr(x)}) (y := {rr(y)}) (by norm_num) ({j} : ℤ) (by norm_num)
  norm_num only [Int.cast_neg, Int.cast_ofNat] at he
  try simp only [div_one]
  rw [he]
  constructor <;> nlinarith [hy.1,hy.2,log_two_certificate.1,log_two_certificate.2]
'''
s+='\nend\nend EntropyConstrainedMissingMass.Certificates\n'
(OUT/'CertificateLogData.lean').write_text(s)
print(f'Generated {len(values)} rational logarithm enclosures.')

s = '''import EntropyConstrainedMissingMass.CertificateLogData
import EntropyConstrainedMissingMass.CertificateRoots

/-! Every stored entropy root and objective bracket in Appendix D, checked in Lean. -/
namespace EntropyConstrainedMissingMass.Certificates
noncomputable section
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
for ci,(hs,t,k,M,rows,winner) in enumerate(C.CASES):
    h=Q(hs)
    s+=f'''
theorem index_{ci} : entropySupportIndex {rr(h)} = {k} := by
  have hl := {values[Q(k)]}
  have hu := {values[Q(k+1)]}
  norm_num only [div_one] at hl hu
  apply entropySupportIndex_eq_of_log_bounds (by norm_num)
  · norm_num only [Nat.cast_ofNat]
    linarith [hl.2]
  · norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith [hu.1]

theorem cutoff_{ci} : candidateCutoff {t} {rr(h)} = {M} := by
  unfold candidateCutoff
  have hc : ⌈({t} : ℝ)*{rr(h)}+1⌉₊ = {C.ceil_fraction(t*h+1)} :=
    (Nat.ceil_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc ⊢
  rw [index_{ci}, hc]
  norm_num
'''
    for branch,m,num in rows:
        a=Q(num,C.DEN);b=Q(num+1,C.DEN)
        tag=f'{ci}_{branch}_{m}'
        for z,ab in ((a,'a'),(b,'b')):
            # Direct branch formula requires only log(z) and log((1-z)/m).
            below=(branch=='light')==(ab=='a')
            concl=f'branchEntropy {m} {rr(z)} < {rr(h)}' if below else f'{rr(h)} < branchEntropy {m} {rr(z)}'
            s+=f'''
theorem entropy_sign_{tag}_{ab} : {concl} := by
  have hz := {values[z]}
  have hq := {values[(1-z)/m]}
  norm_num [branchEntropy]
  nlinarith [hz.1,hz.2,hq.1,hq.2]
'''
        root=f'lightRoot {rr(h)}' if branch=='light' else f'heavyRoot {rr(h)} {m}'
        s+=f'''
theorem root_{tag} : {root} ∈ Ioo {rr(a)} {rr(b)} := by
'''
        if branch=='light':
            s+=f'''  apply lightRoot_mem_of_entropy_signs (by norm_num)
  · rw [index_{ci}]; norm_num
  · rw [index_{ci}]; norm_num
  · simpa only [index_{ci}, Nat.cast_ofNat] using entropy_sign_{tag}_a
  · simpa only [index_{ci}, Nat.cast_ofNat] using entropy_sign_{tag}_b
'''
        else:
            s+=f'''  exact heavyRoot_mem_of_entropy_signs (by norm_num) (by norm_num [index_{ci}])
    (by norm_num) (by norm_num) entropy_sign_{tag}_a entropy_sign_{tag}_b
'''
        l,u=C.objective_bounds(a,b,m,t);lo,hi=rounded(l,u,12)
        value=f'lightValue {t} {rr(h)}' if branch=='light' else f'heavyCandidateValue {t} {rr(h)} {m}'
        s+=f'''
theorem value_{tag} : {rr(lo)} < {value} ∧ {value} < {rr(hi)} := by
  have hr := root_{tag}
  have hb := objective_certificate_nat {m} {t} {rr(a)} ({root}) {rr(b)}
    (by norm_num) (by norm_num) hr.1.le hr.2.le (by norm_num)
  {'simp only [lightValue, index_'+str(ci)+', Nat.cast_ofNat]' if branch=='light' else 'unfold heavyCandidateValue'}
  constructor
  · exact lt_of_lt_of_le (by norm_num) hb.1
  · exact lt_of_le_of_lt hb.2 (by norm_num)
'''
s+='\nend\nend EntropyConstrainedMissingMass.Certificates\n'
(OUT/'CertificateRootData.lean').write_text(s)
print('Generated all 24 root brackets, objective enclosures, support indices, and cutoffs.')

s='''import EntropyConstrainedMissingMass.CertificateRootData
import EntropyConstrainedMissingMass.CertificateWinners

/-! Certified failures of unimodality and entropy-monotone optimizer type, Appendix D. -/
namespace EntropyConstrainedMissingMass.Certificates
noncomputable section
open Set
'''
for ci,(hs,t,k,M,rows,winner) in enumerate(C.CASES):
    h=Q(hs);br,win=winner;wt=f'{ci}_{br}_{win}'
    heavies=[r for r in rows if r[0]=='heavy']
    heavywin=max(heavies,key=lambda row:C.objective_bounds(Q(row[2],C.DEN),Q(row[2]+1,C.DEN),row[1],t)[0])[1]
    s+=f'''
theorem heavy_comparisons_{ci} (j : ℕ) (hj : entropySupportIndex {rr(h)} ≤ j)
    (hM : j ≤ candidateCutoff {t} {rr(h)}) (hne : j ≠ {heavywin}) :
    heavyCandidateValue {t} {rr(h)} j < heavyCandidateValue {t} {rr(h)} {heavywin} := by
  rw [index_{ci}] at hj
  rw [cutoff_{ci}] at hM
  have hw := value_{ci}_heavy_{heavywin}
  interval_cases j
'''
    for j in range(k,M+1):
        s+= '  · exact (hne rfl).elim\n' if j==heavywin else f'  · linarith [value_{ci}_heavy_{j}.2,hw.1]\n'
    s+=f'''
theorem heavy_maximum_{ci} :
    sSup ((heavyCandidateValue {t} {rr(h)}) '' Ici (entropySupportIndex {rr(h)})) =
      heavyCandidateValue {t} {rr(h)} {heavywin} := by
  apply heavy_sup_eq_of_comparisons (by norm_num) (by norm_num) (by norm_num [index_{ci}])
  intro j hj hM
  by_cases he : j = {heavywin}
  · subst j; rfl
  · exact (heavy_comparisons_{ci} j hj hM he).le
'''
    if br=='light':
        s+=f'''
theorem light_comparisons_{ci} (j : ℕ) (hj : entropySupportIndex {rr(h)} ≤ j)
    (hM : j ≤ candidateCutoff {t} {rr(h)}) :
    heavyCandidateValue {t} {rr(h)} j < lightValue {t} {rr(h)} := by
  rw [index_{ci}] at hj
  rw [cutoff_{ci}] at hM
  have hw := value_{wt}
  interval_cases j
'''
        for j in range(k,M+1):s+=f'  · linarith [value_{ci}_heavy_{j}.2,hw.1]\n'
        s+=f'''
theorem optimal_value_{ci} : optimalValue {t} {rr(h)} = lightValue {t} {rr(h)} :=
  optimalValue_eq_light_of_comparisons (by norm_num) (by norm_num)
    (fun j hj hM => (light_comparisons_{ci} j hj hM).le)

theorem unique_optimizer_{ci} {{ι : Type*}} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible {rr(h)} ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible {rr(h)} → q.objective {t} ≤ p.objective {t}) ↔
        ProbabilityVector.LightCandidateForm {rr(h)} p :=
  p.globalMax_iff_light_of_strict_comparisons (by norm_num) (by norm_num) light_comparisons_{ci}
'''
    else:
        s+=f'''
theorem light_loses_{ci} : lightValue {t} {rr(h)} < heavyCandidateValue {t} {rr(h)} {win} := by
  linarith [value_{ci}_light_{k}.2,value_{wt}.1]

theorem optimal_value_{ci} : optimalValue {t} {rr(h)} = heavyCandidateValue {t} {rr(h)} {win} := by
  apply optimalValue_eq_heavy_of_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_{ci}]) (by norm_num [cutoff_{ci}]) light_loses_{ci}.le
  intro j hj hM
  by_cases he : j = {win}
  · subst j; rfl
  · exact (heavy_comparisons_{ci} j hj hM he).le

theorem unique_optimizer_{ci} {{ι : Type*}} [Countable ι] [Infinite ι] (p : ProbabilityVector ι) :
    (p ∈ ProbabilityVector.Feasible {rr(h)} ∧ ∀ q : ProbabilityVector ι,
      q ∈ ProbabilityVector.Feasible {rr(h)} → q.objective {t} ≤ p.objective {t}) ↔
        p.HeavyCandidateAt {rr(h)} {win} :=
  p.globalMax_iff_heavy_of_strict_comparisons (by norm_num) (by norm_num)
    (by norm_num [index_{ci}]) (by norm_num [cutoff_{ci}]) light_loses_{ci} heavy_comparisons_{ci}
'''
s+='''
/-- The three certified heavy entries form a strict valley, precluding unimodality. -/
theorem nonunimodal_example :
    heavyCandidateValue 8 (19/8) 11 < heavyCandidateValue 8 (19/8) 10 ∧
      heavyCandidateValue 8 (19/8) 11 < heavyCandidateValue 8 (19/8) 12 := by
  constructor <;> linarith [value_3_heavy_10.1,value_3_heavy_11.2,value_3_heavy_12.1]

/-- The displayed global optimum bracket at h=19/8. -/
theorem global_value_19_8 :
    (458686581808 : ℝ)/10^12 < optimalValue 8 (19/8) ∧
      optimalValue 8 (19/8) < (458686581809 : ℝ)/10^12 := by
  rw [optimal_value_3]
  convert value_3_heavy_14 using 1 <;> norm_num

end
end EntropyConstrainedMissingMass.Certificates
'''
(OUT/'CertifiedExamples.lean').write_text(s)
print('Generated strict comparison and unique optimizer theorems for all four cases.')
