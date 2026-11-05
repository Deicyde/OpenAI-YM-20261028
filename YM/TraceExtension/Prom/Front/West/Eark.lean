import YM.MergeProof.West.Eark
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision RG Filter
open Further.FreeCovariance.KP
open Next.Rank Next.Rank.Atlas Next.Rank.Radian Next.Rank.Perch Next.Rank.CellsInt Next.Rank.Station
open scoped Topology BigOperators

section pre
variable {K : KernelChoices} (P : Prisms K)

variable {u:ℕ}
private lemma increase_train {G:Gauge}{P:Schedule}{i d j:ℕ}{K:AtlasData G P i}{a b:ℝ} (h : Radian.Train K j d a) (he:a ≤ b) : Radian.Train K j d b:=by
  refine { h with optic:= fun k hk f v hv he' t ht=> ?_ }
  apply (h.optic k hk f v hv he' t ht).trans
  gcongr
  exact pow_nonneg (div_nonneg (P.a_pos _).le (P.a_pos _).le) _

-- a price uniform over both adjacent J calls, obtained *before* L
private def EarnsSky (K:KernelChoices)(J I:ℕ)(C:ℝ):Prop:= 1 ≤ C ∧ (4 ≤ J → 4 ≤ I → ∀ {G:Gauge} (A:Levels G), A.clock.kernel=K→ ∀ N i p d,A.clock.J (i+1)=J → A.clock.J i=I → d-1 ≤ J-2 → Radian.Train (stamp A N p) i d C)
private lemma aheadSky (K:KernelChoices)(J I:ℕ) : ∃ C,EarnsSky K J I C:=by
   by_cases h: 4 ≤ J ∧ 4 ≤ I
   · obtain ⟨C,hC,h⟩:= train_issue K J I h.1 h.2; exact ⟨C,hC,fun _ _=> @h⟩
   exact ⟨1,le_rfl,fun he hp {G}=> (h ⟨he,hp⟩).elim⟩
def pairsSky (K : KernelChoices) (J I : ℕ):ℝ := Classical.choose (aheadSky K J I)
lemma pairsSky_at (K:KernelChoices)(J I:ℕ): 1 ≤ pairsSky K J I:= (aheadSky K J I).choose_spec.1

def trainSky (K:KernelChoices)(J:ℕ):= max (pairsSky K J J) (max (pairsSky K J (J-1)) (pairsSky K (J-1) (J-1)))
lemma trainSky_at (K:KernelChoices)(J:ℕ) : 1 ≤ trainSky K J:= (pairsSky_at K J J).trans (le_max_left ..)

structure EarkSky (P:Prisms K)(u J d D : ℕ) (b L s:ℝ):Prop where
  optics n (h : n≤u) : trainSky K J ^ bump L b s * (2:ℝ)^d ≤ fraction n D s
  front : P.glass J d ≤ Perch.bill (1/4) s
  hinge n (h : n≤u) : max (P.centers J) (P.centers (J-1)) ≤ fraction n D s

variable {G : Gauge} {b : ℝ} (A : Levels G) (hA : A.clock.kernel=K)
variable {d D k : ℕ}
include hA
theorem y_supplySky (h : AllowedSky A b k) (ht : d-1 ≤ A.clock.J k -1 -2) (he : EarkSky P u (A.clock.J k) d D b (wheelSky A k) (clim A k)) (N p : ℕ):
    Seal A k p d 2 (stamp A N p) chartHeat ∧ ∀ n : ℕ, n ≤ u → Worker.Folded k (middleSky A b k) p D A (stamp A N p) d n := by
  let J := A.clock.J k; have hJ:4≤J:= A.clock.adm k; let l:=middleSky A b k
  have hz (i:ℕ) (hl : middleSky A b k ≤ i) (hi:i ≤ k) : A.clock.J i=J ∨ A.clock.J i=J-1:= by
     have hp:=h.bracket i ((widerSky ..).trans hl) hi; have hv:=A.fits.mono hi; change _ ≤ J at hv; change J-1 ≤ _ at hp; omega
  have hv:= hz l le_rfl (beforeSky ..)
  have hl: P.centers (A.clock.J l) ≤ max (P.centers J) (P.centers (J-1)):= hv.elim (fun h=> by rw [h]; exact le_max_left ..) (fun h=> by rw [h]; exact le_max_right ..)
  refine ⟨P.locks J d hJ _ hA N k p rfl he.front,fun n hn=> ?_⟩
  refine ⟨stamp_real A N k p,stamp_real A N l p, fun i=>rows_close A N p l i, fun i j=> (P.earns _ (A.clock.adm l) A hA N l p rfl i j).trans (hl.trans (he.hinge n hn)),
    trainSky K J,trainSky_at ..,(le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (trainSky_at ..) h.full) (by norm_num)) (he.optics n hn)),fun i hi hp=>?_⟩
  let x:=A.clock.J (i+1); let y:=A.clock.J i
  have hv:x=J ∨ x=J-1:= hz _ (hi.trans (Nat.le_succ _)) hp
  have hK:= hz _ hi hp.le; change y=J ∨ y=J-1 at hK; have hh:y≤x:=A.fits.mono (Nat.le_succ _); change d-1 ≤ J-1-2 at ht
  have ht := (aheadSky K x y).choose_spec.2 (A.clock.adm (i+1)) (A.clock.adm i) A hA N i p d rfl rfl (by omega)
  apply increase_train ht
  change pairsSky K x y ≤ max _ _; rcases hv with he|he
  · rw [he]; rcases hK with hk|hk
    · rw [hk]; exact le_max_left ..
    rw [hk]; exact (le_max_left ..).trans (le_max_right ..)
  rw [show y=J-1 by omega,he]; exact (le_max_right ..).trans (le_max_right ..)
end pre
end YM.PhysicalNext.RankCovariance
