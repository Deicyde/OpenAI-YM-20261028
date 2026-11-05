import YM.Next.RANK.Axial
import YM.Next.RANK.Haar
import YM.Vac.Shelter
import YM.Work.F05.Actions




/-!
# Root pricing: true extensive determinant costs (terminal law)

Numerator here still unnormalized; complex amplitudes permitted. This theorem is
useful when the number of copies is the volume of the terminal torus in the
propagated representation. It is not tied to a canonical schedule/ordinary
threshold -- e.g. it can be used on a restarted step. No fourth-wall or
flags ignored in the proof of vacuum lower bound. Compare .
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank
open Lattice Wilson RG Axial MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal

/-- Keep fixed, across stages and volumes. -/
structure HaarBudget (G : Gauge) where
  small : ℝ
  big : ℝ
  positive : 0 < small
  small_le : small ≤ 1
  big_ge : 1 ≤ big
  low (r : ℝ) : 0 < r → r ≤ 1 → small*r^G.lieDim ≤ G.probHaar.real (G.shell (r/4))
  high (t : ℝ) : 0 < t → (∫ u, Real.exp (-(G.chord u/t)) ∂G.probHaar) ≤ big*t^G.lieDim

lemma exists_budget (G : Gauge) : Nonempty (HaarBudget G) := by
  obtain ⟨a,b,h,j,k,l,t⟩ := integral_budget G; exact ⟨⟨a,b,h,j,k,l,t⟩⟩

variable {G : Gauge} {n : Side} {R : Rep G n} {σ A Λ δ w : ℝ} (h : R.Lawful σ A Λ δ w)

private lemma mask_law {X : Type*} [Zero X] (t : ℝ) (S : Support n) (F : Config G n → X) (hf : GaugeInvariant F) :
    GaugeInvariant (masked t S F) := by intro k U; classical simp [masked,indicator,Healthy,hf k U]

include h

/-- Gauge invariance of the entire unmarked density. -/
theorem gauge_eval : GaugeInvariant R.eval := by
  have hA {m} (f : ℕ → Atom G m) (H : ∀ i,(f i).Invariant) (U : Config G n) (k : Site n → G.El) (x : Site n) :
      PathData.atomSeries f R.p (Lattice.gauge k U) x=PathData.atomSeries f R.p U x := by
    apply tsum_congr; intro i
    refine mask_law _ _ (fun U => (f i).unmasked U x) (fun g W => ?_) k U
    simp only [Atom.unmasked,Work.F05.slot_gauge]; exact H i (g x) _
  have hP (p : Face (Per n)) (U : Config G n) (k : Site n → G.El) : R.path.baseTerm R.clip R.p (gauge k U) p = R.path.baseTerm R.clip R.p U p := by
    classical
    have he : PathData.kept R.clip R.p.threshold p.1 (gauge k U) ↔ PathData.kept R.clip R.p.threshold p.1 U := by simp [PathData.kept]
    simp only [PathData.baseTerm,face_gauge,G.chord_conj,he,Work.F05.ell_gauge h.paths,G.norm_adjoint]
  have he : GaugeInvariant R.exponent := by
    intro k U
    have piece (i : ℕ) : R.activities.regularOccurrence R.p i (gauge k U) = R.activities.regularOccurrence R.p i U :=
      mask_law _ _ _ (h.labels.regular.smooth i).symmetry k U
    simp only [Rep.exponent,PathData.inChannels,PathData.principal,Work.F05.pull_gauge_zero,hP,
      hA R.path.cubic (fun i => (h.paths.invariant i).2.1),hA R.path.quartic (fun i => (h.paths.invariant i).2.2),
      hA R.path.loop (fun i => (h.paths.invariant i).1),Activities.additive,piece]
  intro k U
  have HK (i : ℕ) := h.labels.forced.sym i k U
  classical
  have hg (i : Finset ℕ) : R.activities.admissible R.p (gauge k U) i ↔ R.activities.admissible R.p U i := by
    unfold Activities.admissible; rw [gauge_flags]
  simp only [Rep.eval, he k U, Activities.gas, Activities.gasOccurrence,hg,HK]

omit h
private lemma beta_pos (g : ℝ) (he : R.beta*g^2=1) : 0<R.beta := by
  by_contra! h; have hh := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg g); linarith

include h

theorem vacuum_bound (O : HaarBudget G) (hn : ∀ U,0≤R.eval U) {g : ℝ} (hg : 0<g) (hr : g ≤ R.p.threshold) (hy : R.beta*g^2=1) :
    Real.exp (R.scalar-(Fintype.card (Site n):ℝ)*(R.exCost A Λ δ+R.beta*baseBudget R.clip A g)) *
      (O.small*g^G.lieDim)^(3*Fintype.card (Site n)+1) ≤ ∫ U,R.eval U∂prior G n := by
  classical
  let T := Axial.axle n
  let K := Set.pi Set.univ fun _ : T.Free => G.shell (g/4)
  let q := 3*Fintype.card (Site n)+1
  have hq : Fintype.card T.Free=q := Axial.free_count n
  have hk : MeasurableSet K := MeasurableSet.univ_pi fun _ => G.shell_meas _
  let D := R.scalar-(Fintype.card (Site n):ℝ)*(R.exCost A Λ δ+R.beta*baseBudget R.clip A g)
  have he : ∀ S∈ K, Real.exp D ≤ R.eval (T.drape S) := by
    intro S hs
    have hu : T.drape S ∈ RG.calm G n g := by
      intro i _
      change G.chord (T.drape S i) ≤ _
      by_cases h : i∈T.trunks
      · rw [show T.drape S i=1 from T.on_tree S ⟨i,h⟩,G.chord_one]; positivity
      rw [show T.drape S i=S ⟨i,h⟩ from T.off_tree S ⟨i,h⟩]; exact hs ⟨i,h⟩ (mem_univ _)
    rw [Rep.eval,Activities.gas_one _ _ (RG.voids hu hr),mul_one]
    exact Real.exp_monotone (R.exponent_lo h (beta_pos g hy).le _ hg hr hu)
  have hI : Integrable (fun U => R.eval (T.drape U)) (T.order G) := by
    obtain ⟨C,hC⟩ := (R.envelope h).cost
    exact Integrable.of_bound ((R.envelope h).meas.comp T.continuous_drape.measurable).aestronglyMeasurable C (Eventually.of_forall fun i => hC _)
  rw [T.pack R.eval ((R.envelope h).integrable _) (fun k _ => gauge_eval h k)]
  change Real.exp D * _ ≤ _
  calc
    _ ≤ (T.order G).real K * Real.exp D := by
      rw [mul_comm _ (Real.exp D)]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      unfold K Tree.Forest.order
      rw [measureReal_def,Measure.pi_pi,Finset.prod_const,Finset.card_univ,hq,ENNReal.toReal_pow]
      exact pow_le_pow_left₀ (mul_nonneg O.positive.le (by positivity)) (O.low _ hg (hr.trans R.p.threshold_le)) _
    _ = ∫ U, K.indicator (fun _ => Real.exp D) U∂T.order G := by rw [integral_indicator hk, setIntegral_const]; rfl
    _ ≤ _ := integral_mono (integrable_const _|>.indicator hk) hI fun S => by
      by_cases hs : S∈ K
      · rw [indicator_of_mem hs]; exact he _ hs
      rw [indicator_of_notMem hs]; exact hn _

omit h

/-- Direct-face prices. No hypothesis from Γδ / near flag. -/
def strength (p : Clip) := min 1 p.linear
lemma strength_pos (p : Clip) : 0 < strength p := lt_min zero_lt_one p.tail_pos
lemma strength_le_one (p : Clip) : strength p ≤ 1 := min_le_left ..

private lemma base_price {g : ℝ} (hg : 0<g) (hm : R.beta*g^2=1) (he : g≤R.p.threshold) (U : Config G n) (p : Face (Per n)) :
    G.chord (faceValue U p) / (g / strength R.clip) - 1 ≤ R.beta*R.path.baseTerm R.clip R.p U p := by
  let c := strength R.clip
  let a := G.chord (faceValue U p)
  have hc : 0 < c := strength_pos R.clip
  have hn : 0 ≤ a := G.chord_nonneg _
  have hp : 0 < R.beta := beta_pos g hm
  have hq : c ≤ R.clip.linear := min_le_right ..
  have ht : c ≤ R.clip.direct := by have := R.clip.kink; linarith
  have heq : a/(g/c)=c*(a/g) := by field_simp
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (show PathData.clipped R.clip R.p.threshold a ≤ _ from ?_) hp.le)
  · change a/(g/c) - _ ≤ _; rw [heq]; unfold PathData.clipped
    split_ifs with HF
    · calc
        _ ≤ c*((a/g)^2)/2 := by
          have hj : 0 ≤ c*((a/g)-1)^2 := mul_nonneg hc.le (sq_nonneg _)
          have hv : c ≤ 1 := strength_le_one _
          nlinarith only [hj, hv]
        _ = R.beta * (c*a^2/2) := by rw [show R.beta=1/g^2 from (eq_div_iff (pow_ne_zero _ hg.ne')).2 hm]; ring
        _ ≤ R.beta * (R.clip.direct * a^2 / 2) := by gcongr
    · calc
        _ ≤ c * (a/g) := by linarith only
        _ ≤ R.beta * (R.clip.linear*g*a) := by
          have hs : 0≤a/g := div_nonneg hn hg.le
          apply le_trans (mul_le_mul_of_nonneg_right hq hs); apply le_of_eq
          rw [show R.beta=1/g^2 from (eq_div_iff (pow_ne_zero _ hg.ne')).2 hm]; field_simp
        _ ≤ _ := by gcongr; exact R.clip.tail_pos.le
  classical
  unfold PathData.baseTerm
  split <;> simp [a]; positivity

include h

lemma exponent_retains {g : ℝ} (hg : 0<g) (he : g≤R.p.threshold) (hm : R.beta*g^2=1) (U : Config G n) :
    R.exponent U ≤ R.scalar+(Fintype.card (Site n):ℝ)*(R.exCost A Λ δ + Fintype.card PlaqAxes)-
      ∑ p : Face (Per n), G.chord (faceValue U p)/(g/strength R.clip) := by
  let Gc := g/strength R.clip
  let F (W : Config G n) := ∑ p : Face (Per n), G.chord (faceValue W p) / Gc
  have s (k : Signed) : F (pull k 0 U)=F U := by
    unfold F; simp_rw [Face.send_price U _ k 0 G.chord G.chord_inv (fun _ u => G.chord_conj u _)]
    let e : Equiv.Perm (Face (Per n)) := Equiv.ofBijective (Face.send k 0) ⟨Face.injective_send k 0,
      Finite.injective_iff_surjective.mp (Face.injective_send k 0)⟩
    exact Equiv.sum_comp e (fun x => G.chord (faceValue U x)/Gc)
  let q : ℝ := Fintype.card (Site n)
  let a : ℝ := Fintype.card PlaqAxes
  let v := PathData.loopsPrice R.p R.beta A Λ
  have heq (W : Config G n) : (∑ p : Face (Per n), (G.chord (faceValue W p)/Gc-1))=F W - q*a := by
    unfold F q a; rw [Finset.sum_sub_distrib]; simp [Face,Site]
  have hf (k : Signed) : F U - q*a-q*v ≤ R.path.principal R.clip R.p R.beta (pull k 0 U) := by
    let W := pull k 0 U
    have H := Finset.sum_le_sum fun i (_:i∈Finset.univ) => base_price hg hm he W i
    change (∑ p : Face (Per n), (G.chord (faceValue W p)/Gc-1))≤_ at H
    rw [← Finset.mul_sum,heq,s k] at H
    have hj := (abs_le.mp (R.path.volume_price R.clip R.p _ (beta_pos g hm).le W h.paths)).1
    change -(q*v) ≤ _ at hj
    linarith only [hj,H]
  have huv := (Branch.avg_const (n:=Signed) (F U-q*a-q*v)).symm.le.trans (Branch.avg_mono hf)
  have hh := (abs_le.mp (volumeE R.activities h.labels U)).1
  change F U - q*a-q*v ≤ R.path.inChannels R.clip R.p R.beta U at huv
  change -(q*δ) ≤ _ at hh
  change R.scalar-R.path.inChannels R.clip R.p R.beta U-_ ≤ R.scalar+q*((δ+v)+a)-F U
  linarith only [huv, hh]

section numerator

open Real

/-- Use with marker price *before* integrating. `X` is an additive bill per site in this
terminal array, not yet a per-site cost on the original N. -/
theorem numerator (O : HaarBudget G) (hn : 1<n.val) {g X z : ℝ} (hg : 0<g) (he : g≤R.p.threshold) (hm : R.beta*g^2=1)
    (F : Config G n → ℂ) (hI : Integrable F (prior G n)) (hz : 0 ≤ z) (H : ∀ U, z*‖F U‖≤ Real.exp (R.exponent U+(Fintype.card (Site n):ℝ)*X)) :
    z*‖∫ U,F U ∂prior G n‖ ≤
      Real.exp (R.scalar+(Fintype.card (Site n):ℝ)*(R.exCost A Λ δ + Fintype.card PlaqAxes + X)) *
        (O.big*(g/strength R.clip)^G.lieDim)^(3*Fintype.card (Site n)-3) := by
  let E := g/strength R.clip
  let v u := Real.exp (-(G.chord u/E))
  have hp : 0<E := div_pos hg (strength_pos _)
  have hB (u) : v u ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (G.chord_nonneg _) hp.le))
  have hv : Continuous v := by unfold v; fun_prop
  let q : ℝ := Fintype.card (Site n)
  let a : ℝ := Fintype.card PlaqAxes
  let D := R.scalar+q*(R.exCost A Λ δ+a+X)
  calc
    _ ≤ z*(∫ U, ‖F U‖ ∂prior G n) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hz
    _ = ∫ U, z*‖F U‖ ∂prior G n := (integral_const_mul _ _).symm
    _ ≤ ∫ U : Config G n, Real.exp D * (∏ p : Face (Per n), v (faceValue U p)) ∂prior G n := by
      refine integral_mono (hI.norm.const_mul _) (Integrable.const_mul ?_ _) fun U => (H U).trans ?_
      · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        exact continuous_finsetProd _ fun i _ => hv.comp (continuous_travel _ _)
      unfold v
      rw [← Real.exp_sum,← Real.exp_add,Finset.sum_neg_distrib]
      apply Real.exp_monotone; have hb := exponent_retains h hg he hm U
      change R.exponent U ≤ R.scalar+q*(R.exCost A Λ δ+a)- ∑ p, G.chord (faceValue U p) / E at hb
      change R.exponent U+q*X ≤ D+_
      unfold D; linarith only [hb]
    _ = Real.exp D * (∫ U : Config G n, (∏ p : Face (Per n),v (faceValue U p))∂prior G n) := by rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((elimination hn v hv (fun u => (Real.exp_pos _).le) hB).trans
      (pow_le_pow_left₀ (integral_nonneg fun i => (Real.exp_pos _).le) (O.high E hp) _)) (Real.exp_pos _).le

-- log notation real
def ent (O : HaarBudget G) (p : Clip) := Real.log O.big - G.lieDim * Real.log (strength p)

/-- For comparisons it suffices with a slightly larger per site estimate but at the
right power of `g`. Every variable here belongs to its current query; no earlier
scale/constant reused. -/
def protection (O : HaarBudget G) (R : Rep G n) (A Λ δ X g : ℝ) :=
    2*R.exCost A Λ δ + Fintype.card PlaqAxes + R.beta*baseBudget R.clip A g + X +
      3*ent O R.clip-4*Real.log O.small

omit h in
private lemma to_upper {p : Clip} (O : HaarBudget G) (k : ℕ) {g : ℝ} (hg : 0<g) :
    (O.big*(g/strength p)^G.lieDim)^k=Real.exp ((k:ℝ)*(ent O p + G.lieDim*Real.log g)) := by
  have h₁ := (lt_of_lt_of_le zero_lt_one O.big_ge)
  have h₂ : 0 < strength p := strength_pos p
  rw [Real.exp_nat_mul]
  congr 1
  unfold ent
  have hD : Real.log O.big - G.lieDim*Real.log (strength p)+ G.lieDim*Real.log g = Real.log O.big+ G.lieDim*Real.log (g/strength p) := by rw [Real.log_div hg.ne' h₂.ne']; ring
  rw [hD,Real.exp_add,Real.exp_log h₁,Real.exp_nat_mul,Real.exp_log (div_pos hg h₂)]

theorem determinant (O : HaarBudget G) (hn : ∀ U,0≤R.eval U) (hn' : 1 < n.val) {g X z : ℝ}
    (hg : 0<g) (he : g≤R.p.threshold) (hm : R.beta*g^2=1)
    (F : Config G n → ℂ) (hI : Integrable F (prior G n)) (hz : 0 ≤ z)
    (H : ∀ U,z*‖F U‖ ≤ Real.exp (R.exponent U+(Fintype.card (Site n):ℝ)*X)) :
    z * ‖∫ U,F U ∂prior G n‖ / (∫ U, R.eval U∂prior G n) ≤
      Real.exp ((Fintype.card (Site n):ℝ)*protection O R A Λ δ X g-
        4 * G.lieDim * Real.log g) := by
  let c := Fintype.card (Site n)
  let u := 3*c-3
  let l := 3*c+1
  let d := G.lieDim
  have hc : 0<c := Fintype.card_pos
  have ho := O.positive
  have hv := vacuum_bound h O hn hg he hm
  have hp : 0 < ∫ U, R.eval U∂prior G n := lt_of_lt_of_le (by positivity) hv
  rw [div_le_iff₀ hp]
  apply (numerator h O hn' hg he hm F hI hz H).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le)
  rw [to_upper O _ hg,show (O.small*g^d)^l=Real.exp ((l:ℝ)*(Real.log O.small+d*Real.log g)) by
    rw [Real.exp_nat_mul,Real.exp_add,Real.exp_nat_mul,Real.exp_log hg,Real.exp_log ho]]
  rw [← Real.exp_add,← Real.exp_add, ← Real.exp_add]; apply Real.exp_monotone
  let r := R.exCost A Λ δ; let s : ℝ := Fintype.card PlaqAxes; let a := R.beta*baseBudget R.clip A g
  let Q := ent O R.clip; let L := Real.log O.small; let D := d*Real.log g
  have hx : L ≤ 0 := Real.log_nonpos ho.le O.small_le
  have hQ : 0 ≤ Q := sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (Real.log_nonpos (strength_pos _).le (strength_le_one _))).trans (Real.log_nonneg O.big_ge))
  have hl : (l:ℝ)=(u:ℝ)+4 := by
    exact_mod_cast (show l=u+4 by dsimp [l,u]; omega)
  have hu : (u:ℝ) ≤ 3*(c:ℝ) := by exact_mod_cast (show u≤3*c by unfold u;omega)
  have hi : (l:ℝ) ≤ 4*(c:ℝ) := by exact_mod_cast (show l≤4*c by unfold l;omega)
  rw [mul_assoc 4]
  change R.scalar + (c:ℝ)*(r+s+X)+ (u:ℝ)*(Q+D) ≤ (c:ℝ)*(2*r+s+a+X+3*Q-4*L)-4*D+
    (R.scalar-(c:ℝ)*(r+a)+(l:ℝ)*(L+D))
  have hh : (l:ℝ)*D=(u:ℝ)*D+4*D := by rw [hl,add_mul]
  linarith only [hh, mul_le_mul_of_nonneg_right hu hQ, mul_le_mul_of_nonpos_right hi hx]

end numerator
end YM.Next.Rank
