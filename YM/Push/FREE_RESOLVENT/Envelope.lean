import YM.Push.FREE_RESOLVENT.Affine
import YM.Push.FREE_RESOLVENT.Powers
import YM.Work.C13.Decay

/-!
# Real envelopes with small-field cutoff on the input

Translate path norm hypotheses to bounds before period evaluation. No
sup-operator-norm growth at zero-order per untouched unitary! Coordinate
cutoff used only in proof of summability at every derivative order; actual
calls to kernels never change the physical background convention near 0.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f} {k : ℕ} {σ V A : ℝ}

section smooth
variable {τ E F H K : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup K] [NormedSpace ℝ K]
variable {A B r : ℝ} {X Y : E → F} {Z : E → H}

/-- Global derivative cap for the extended real paths. -/
structure Ceiling (k : ℕ) (A : ℝ) (X : E → F) : Prop where
  smooth : ContDiff ℝ k X
  op (l : ℕ) (x) : l ≤ k → ‖iteratedFDeriv ℝ l X x‖ ≤ A

namespace Ceiling
lemma mono (h : Ceiling k A X) (ha : A ≤ B) : Ceiling k B X := ⟨h.smooth, fun i x hi => (h.op i x hi).trans ha⟩
lemma ceiling_const (x : F) : Ceiling k ‖x‖ (fun _ : E => x) := by
  constructor
  · exact contDiff_const
  rintro (_ | i) z he
  · rw [norm_iteratedFDeriv_zero]
  rw [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; exact norm_nonneg _
lemma add (h : Ceiling k A X) (g : Ceiling k B Y) : Ceiling k (A+B) (fun x => X x+Y x) := by
  constructor
  · exact h.smooth.add g.smooth
  intro i y he
  rw [fun_iteratedFDeriv_add_apply (smooth_of_le h.smooth.contDiffAt he) (smooth_of_le g.smooth.contDiffAt he)]
  exact (norm_add_le ..).trans (add_le_add (h.op i y he) (g.op i y he))
lemma scale (h : Ceiling k A X) (r : ℝ) : Ceiling k (‖r‖*A) (fun x => r • X x) := by
  constructor
  · exact h.smooth.const_smul r
  intro i y he
  rw [iteratedFDeriv_const_smul_apply' (smooth_of_le h.smooth.contDiffAt he), norm_smul]
  exact mul_le_mul_of_nonneg_left (h.op i y he) (norm_nonneg _)
lemma pre (h : Ceiling k A X) (L : H →L[ℝ] E) (hm : 0 ≤ A) (he : ‖L‖ ≤ r) (hr : 1 ≤ r) :
    Ceiling k (A*r^k) (fun x => X (L x)) := by
  constructor
  · exact h.smooth.comp L.contDiff
  intro i x hi
  rw [show iteratedFDeriv ℝ i (fun x => X (L x)) x = _ from L.iteratedFDeriv_comp_right h.smooth x (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_mul (h.op _ _ hi) _ (pow_nonneg (norm_nonneg _) _) hm
  exact (pow_le_pow_left₀ (norm_nonneg L) he _).trans (pow_le_pow_right₀ hr hi)
lemma post (h : Ceiling k A X) (L : F →L[ℝ] H) : Ceiling k (‖L‖*A) (fun x => L (X x)) := by
  constructor
  · exact L.contDiff.comp h.smooth
  intro i x hi; rw [show iteratedFDeriv ℝ i (fun x => L (X x)) x = _ from L.iteratedFDeriv_comp_left h.smooth.contDiffAt (by exact_mod_cast hi)]
  apply le_trans _ (mul_le_mul_of_nonneg_left (h.op i x hi) (norm_nonneg L))
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..
lemma bill (h : Ceiling k A X) (ha : 0 ≤ A) (t : τ → E) (ht : ∀ i, ‖t i‖ ≤ 1) (l : List τ) (hl : l.length ≤ k) (x : E) :
    ‖jet t X l x‖ ≤ A := by
  refine (ContinuousMultilinearMap.le_of_opNorm_le (h.op _ x hl) (t ∘ l.get)).trans ?_
  exact mul_le_of_le_one_right ha ((Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ht (l.get i))).trans_eq (by simp))
lemma mul (h : Ceiling k A X) (g : Ceiling k B Z) (p : F →L[ℝ] H →L[ℝ] K) (ha : 0 ≤ A) (hb : 0 ≤ B) :
    Ceiling k (2^k * (‖p‖*A*B)) (fun x => p (X x) (Z x)) := by
  constructor
  · exact contDiff_iff_contDiffAt.mpr fun x => smooth_product p h.smooth.contDiffAt g.smooth.contDiffAt
  intro i x hi
  apply list_op (by positivity)
  intro l v hL he; rw [leibniz v p l (smooth_of_le h.smooth.contDiffAt (hL.le.trans hi)) (smooth_of_le g.smooth.contDiffAt (hL.le.trans hi))]
  refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _ => ‖p‖*A*B) fun j _ => ?_) ?_)
  · let a := lo l j; let b := TestD.hi l j
    let T := jet v X a x; let R := jet v Z b x
    exact ((p T).le_opNorm R).trans (mul_le_mul (((p.le_opNorm T)).trans (mul_le_mul_of_nonneg_left
      (h.bill ha v he a ((len_low l j).trans (hL.le.trans hi)) x) (norm_nonneg _)))
        (g.bill hb v he b ((len_high l j).trans (hL.le.trans hi)) x) (norm_nonneg R) (by positivity))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, TestD.card,Nat.cast_pow, Nat.cast_ofNat,hL]; gcongr; norm_num
end Ceiling
end smooth

section cutoff

def cuff (G : Gauge) : ContDiffBump (0:G.Color) := ⟨1,2,by norm_num,by norm_num⟩
def sleeve (G : Gauge) (v : G.Color) := cuff G v • v
def linen (G : Gauge) (v : G.Color) := G.mat (G.lieExp (sleeve G v))

lemma linen_price (G : Gauge) (k : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ Ceiling k D (linen G) := by
  classical
  let T := fun v : G.Color => G.mat (G.lieExp v)-1
  have he : ContDiff ℝ k T := G.exp_jet.of_le le_top |>.sub contDiff_const
  have hh : ContDiff ℝ k (sleeve G) := by
    have hc : ContDiff ℝ k ⇑(cuff G) := ContDiffBump.contDiff _
    exact hc.smul contDiff_id
  let F := T ∘ sleeve G
  have hF : ContDiff ℝ k F := he.comp hh
  have hp : HasCompactSupport F := HasCompactSupport.comp_left (f:=sleeve G) (g:=T)
    (HasCompactSupport.smul_right (f:=⇑(cuff G)) (f':=id) (ContDiffBump.hasCompactSupport _)) (by simp [T])
  have ht (i : Fin (k+1)) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖iteratedFDeriv ℝ i.val F x‖ ≤ A := by
    let H := iteratedFDeriv ℝ i.val F
    have hH : Continuous H := hF.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_of_lt_succ i.isLt)
    obtain ⟨A,hA⟩ := (((hp.iteratedFDeriv i.val).norm).isCompact_range hH.norm).bddAbove
    exact ⟨max A 0,le_max_right ..,fun x => le_trans (hA ⟨x,rfl⟩) (le_max_left ..)⟩
  choose D hD h using ht
  have hC : Ceiling k (∑ i, D i) F := ⟨hF,fun i x hi =>
      (h ⟨i,Nat.lt_succ_of_le hi⟩ x).trans (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_univ _))⟩
  rw [show linen G = fun x => F x + 1 by funext x; change _=_-1+1; rw [sub_add_cancel]; rfl]
  exact ⟨_,add_nonneg (Finset.sum_nonneg fun i _ => hD i) (norm_nonneg _), hC.add (Ceiling.ceiling_const _)⟩

def file (r : ℕ) (x : Body r n) : Vec G n r →L[ℝ] G.Color :=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body r n => G.Color) x).comp (plain G n r).toContinuousLinearMap

def filePrice (G : Gauge) := ‖((PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex => ℝ)).symm :
    (G.ColorIndex → ℝ) →L[ℝ] G.Color)‖ + 1
lemma file_pos (G : Gauge) : 1 ≤ filePrice G := le_add_of_nonneg_left (norm_nonneg _)
lemma folder (r : ℕ) (x : Body r n) : ‖file (G:=G) r x‖ ≤ filePrice G := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (file_pos G))
  intro b
  let L : (G.ColorIndex → ℝ) →L[ℝ] G.Color := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : G.ColorIndex => ℝ)).symm
  let y := fun j : G.ColorIndex => b (ix x j)
  change ‖L y‖ ≤ _
  refine (L.le_opNorm _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (zero_le_one.trans (file_pos G)))
  · exact le_add_of_nonneg_right zero_le_one
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm b (ix x j)

def rawBackdrop (S : StepData c f) (s : Signed) (B : Vec G c 1) := pull s 0 (replica S.ratio
  (represent fun i => sleeve G (decode B i)))

lemma returns (S : StepData c f) (s : Signed) : rawBackdrop (G:=G) S s =ᶠ[𝓝 0] shone S s := by
  have he : ∀ᶠ B : Vec G c 1 in 𝓝 0, ∀ i, sleeve G (decode B i) = decode B i := by
    apply eventually_all.mpr; intro i
    have hh : Tendsto (file (G:=G) (n:=c) 1 i) (𝓝 0) (𝓝 0) := by simpa using (file (G:=G) (n:=c) 1 i).continuous.tendsto 0
    filter_upwards [hh.eventually (cuff G).eventuallyEq_one] with x hx
    unfold sleeve; rw [show (cuff G) (decode x i)=1 from hx, one_smul]
  filter_upwards [he] with x hx; unfold rawBackdrop shone backdrop; simp_rw [hx]

lemma star_ceiling {τ : Type*} [NormedAddCommGroup τ] [NormedSpace ℝ τ] {F : τ → G.Mat} {V : ℝ} (h : Ceiling k V F) :
    Ceiling k V (fun x => star (F x)) := by
  let L := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).toContinuousLinearMap
  have hp := ContinuousLinearMap.opNorm_le_bound (𝕜:=ℝ) L zero_le_one fun x : G.Mat => by change ‖star x‖ ≤ _; simp
  have hv : 0 ≤ V := le_trans (norm_nonneg _) (h.op k 0 le_rfl)
  exact (h.post L).mono (mul_le_of_le_one_left hv hp)

def spaceD (G : Gauge) (k : ℕ) := max ‖(1:G.Mat)‖ ((linen_price G k).choose*(filePrice G)^k)
lemma space_nn (G : Gauge) (k : ℕ) : 0 ≤ spaceD G k := le_max_of_le_left (norm_nonneg _)

lemma blanket (k : ℕ) (S : StepData c f) (s : Signed) (b : Step) (x : Site f) :
    Ceiling k (spaceD G k) (fun v : Vec G c 1 => G.mat (b.read (rawBackdrop S s v) x)) := by
  have he (i : Edge (Site f)) : Ceiling k (spaceD G k) (fun v : Vec G c 1 => G.mat (replica S.ratio
      (represent fun i => sleeve G (decode v i)) i)) := by
    unfold replica
    split
    · exact (Ceiling.ceiling_const (G.mat 1)).mono (le_max_left ..)
    simp_rw [Work.F03.represent_link]
    exact (((linen_price G k).choose_spec.2).pre (file 1 _) (linen_price G k).choose_spec.1 (folder ..) (file_pos G)).mono (le_max_right ..)
  have hh (d : Step) (x : Site f) : Ceiling k (spaceD G k) (fun v : Vec G c 1 => G.mat
      (d.read (replica S.ratio (represent fun i => sleeve G (decode v i))) x)) := by
    unfold Step.read
    split
    · simp_rw [G.mat_inv]; exact star_ceiling (he _)
    exact he _
  simp_rw [rawBackdrop, Step.pull_read]
  exact hh _ _

lemma tapestry (k : ℕ) (S : StepData c f) (s : Signed) (w : Walk) (x : Site f) (hs : 0 < σ) :
    Ceiling k (patchMoney G k σ (spaceD G k) k * Real.exp (σ*w.length))
      (fun y : Vec G c 1 => G.mat (travel (rawBackdrop S s y) x w)) := by
  constructor
  · exact travel_cd (fun b x => (blanket k S s b x).smooth) w x
  intro i B hi
  apply list_op (mul_nonneg (patch_nn _ _ hs (space_nn ..) k) (Real.exp_pos _).le)
  intro l v h ht
  have hh := assembled_jets (p:=B) (fun b x => (blanket k S s b x).smooth) (space_nn ..) hs
    (fun b x l he => (blanket k S s b x).bill (space_nn ..) v ht l he B) w x l (h.le.trans hi)
  exact hh.trans (mul_le_mul_of_nonneg_right (patch_le hs (space_nn ..) (h.le.trans hi)) (Real.exp_pos _).le)
end cutoff
end YM.FreeResolvent.Affine
