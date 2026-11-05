import YM.Next.FOUNDATIONS.SU2
import YM.Planned.PRIMARY_INTEGRAL_295.HighTable
import YM.Push.LOCAL_SPLITTING.Projection


/-! # Matrix prepayment, including constant and lower families -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Place Carrier Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {j m n d t : ℕ} {F : Labels.Frame G d} {M : Side}
variable (T : SectionData F) {A : Hol G} (h : T.Sound A) (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t)
include h hk hj ht

private lemma meter (hd : d ≤ j) (i : F.Index) (J : Jet G) (hl : n ≤ d) (hm : m≤d) :
    ∃ D : ℝ,0≤D ∧ ∀ P : Flight j t,
      ‖read J (gradePart (m,n) (rawBook T h (stored P k hk ht) (copy F i))).val‖ ≤ D * unitStep P.L^((F.grades i).1) := by
  classical
  let V := Fin n → WardBin.Board G d
  let X := Finset.univ.filter (fun b:V=>WardBin.depth b=m)
  choose! D hD H using fun b:V=> upper_end T h k hk hj ht hd i b
  let u (b:V) : ℂ := read J (∏ l, MvPolynomial.X (WardBin.key (b l)))
  have he b (he : b∈X) := (Finset.mem_filter.mp he).2.trans_le hm
  refine ⟨∑ b∈X,D b*‖u b‖,Finset.sum_nonneg
    (fun i hi=>mul_nonneg (hD i (he _ hi)) (norm_nonneg _)),fun P=> ?_⟩
  let g := seen T (copy F i) (linesOf P k)
  have hg := seen_safe T h (stored P k hk ht) (copy F i)
  change ‖read J (gradePart _ (Parts.archive hg)).val‖ ≤ _
  rw [Parts.capture hg hm hl,WardBin.tile,map_sum,Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i Hi=>?_)
  rw [map_mul]
  simp only [Labels.read,MvPolynomial.aeval_C,Algebra.algebraMap_self,RingHom.id_apply,norm_mul]
  refine (mul_le_mul_of_nonneg_right (H i (he i Hi) P) (norm_nonneg _)).trans_eq ?_; unfold u Labels.read; ring

lemma fare (hd : d≤j) (i : F.Index) (p : Push.Local.Probe G d) :
    ∃ C:ℝ,0≤C ∧ ∀ P : Flight j t,
      ‖Push.Local.runProbe F p (receipt T h (stored P k hk ht) (copy F i))‖ ≤ C*unitStep P.L^((F.grades i).1) := by
  classical
  let J := p.1; let m:ℕ:=p.2.val; have hm:m≤d := Nat.le_of_lt_succ p.2.isLt
  choose! D hD H using fun n (hn:n≤d)=> meter T h k hk hj ht hd i J hn hm
  let K := ∑ n∈Finset.range (d+1),D n
  have hK : 0≤K:= Finset.sum_nonneg fun i hi=> hD i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  let v := (m.factorial:ℝ); have hv : 0<v := by unfold v; positivity
  refine ⟨v*K,mul_nonneg hv.le hK,fun P=>?_⟩
  let B:=rawBook T h (stored P k hk ht) (copy F i)
  rw [Push.Local.runProbe_eq]; change ‖iteratedDeriv m (fun t=> read (scaleJet J t) (F.coords.symm (F.coords B)).val) 0‖≤ _
  simp_rw [LinearEquiv.symm_apply_apply]; let g (x : ℝ):=read (scaleJet J x) B.val
  change ‖iteratedDeriv m g 0‖ ≤ _
  rw [show iteratedDeriv m g 0=v • WardBin.leading m g from by
    unfold WardBin.leading; rw [smul_smul, show v * (m.factorial:ℝ)⁻¹=1 from mul_inv_cancel₀ hv.ne',one_smul]]
  unfold g; rw [Parts.scaled_label_leads B hm J, norm_smul,Real.norm_of_nonneg hv.le,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hv.le; unfold K; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun n hn=>?_)
  exact H n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) P

/-- Entry bounds before applying threshold factors. *Not* a claim about
inverting the history factory. Sockets will use exactly these entries. -/
theorem preBill (hd : d≤j) : ∃ C : ℝ,1≤C ∧ ∀ P : Flight j t, ∀ i b,
    ‖receipt T h (stored P k hk ht) (copy F i) b‖≤ C*unitStep P.L^((F.grades i).1) := by
  classical
  choose D hD H using fun i p=>fare T h k hk hj ht hd i p
  obtain ⟨S,C,hC,hq⟩:= Push.Local.probe_budget F
  let s (i) := ∑ p∈ S,D i p; let Z := 1+∑ i,s i
  have hs : ∀ i, 0 ≤ s i := fun i=> Finset.sum_nonneg fun j _=> hD i j
  have hZ : 1≤Z := le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> hs i)
  have hz i p (hp:p∈S) : D i p≤ Z := (Finset.single_le_sum (fun j _=>hD i j) hp).trans
    ((Finset.single_le_sum (fun i _=>hs i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one))
  refine ⟨C*Z,one_le_mul_of_one_le_of_one_le hC hZ,fun P i b=>?_⟩
  let r := receipt T h (stored P k hk ht) (copy F i)
  have hp := unitStep_pos P.L
  calc
    ‖r b‖ ≤ _ := (norm_le_pi_norm r b).trans (Push.Local.norm_le_size F _)
    _ ≤ C*(Z*unitStep P.L^((F.grades i).1)) := hq r _ (by positivity) fun p hp'=> (H i p P).trans
       (mul_le_mul_of_nonneg_right (hz i p hp') (by positivity))
    _ = _ := (mul_assoc ..).symm
end YM.Planned.PrimaryIntegral295.Film
