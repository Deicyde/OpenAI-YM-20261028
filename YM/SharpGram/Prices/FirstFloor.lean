import YM.SharpGram.Prices.Origin
import YM.PertExtension.PureBasis
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size

/-!
# Gap transverse to unit

For simple gauge group use gap all the way to 4. No (epsilon power, or
stage-dependent additive log power) loss on transverse outlet through w=3;
genuine Field functional bound on any horizon. Not yet w ≥ 4. Useful even
applying to weight 4 functionals with allowed engineering consumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter Lattice RG Wilson Labels Source Work.G08 Bid Extra.Histories MergeProof
open Push.Local OPE OPE.Columns Next.UVStress
open scoped Topology BigOperators
variable {G : Gauge} {d : ℕ} (F : Labels.Frame G d) (hG : G.Simple)
set_option quotPrecheck false
local notation "μ" => F.coeffSize

open PertExtension.Horizon
include hG
lemma toFirst (i : F.Index) (h : i ≠ 0) : 4 ≤ (F.grades i).1 := by
  by_contra! hf
  obtain ⟨c,hv⟩ := UVNext.FreeStress.just_one hG hf (lowered F i)
  have ht : F.basis i=c • Labels.unit G d := by rw [← reascend,hv,map_smul]; rfl
  have he : F.coords (F.basis i) i=0 := by rw [ht,map_smul,F.coords_unit]; simp [Frame.e0,h]
  rw [F.coords_basis] at he; simp at he
lemma upToFirst (x : F.Coeff) (L : Side) :
    μ (vowel F L (F.core x)) ≤ (L.val:ℝ) ^ (d-4) * μ (F.core x) := by
  unfold Frame.coeffSize
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [vowel,norm_mul,norm_pow,Complex.norm_natCast]
  rcases eq_or_ne j 0 with h|h
  · simp [h,Frame.core]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast L.pos) ?_) (norm_nonneg _)
  exact Nat.sub_le_sub_left (toFirst F hG j h) d

lemma beforeFirst (x : F.Coeff) (hd : d ≤ 3) : F.core x = 0 := by
  funext i
  have hh : i=0 := by by_contra hh; have h := toFirst F hG i hh; have he := F.bound i; omega
  rw [hh]
  simp [Frame.core]

variable {F} {x y : F.Coeff → F.Coeff} {H : History G} {W : Worth} {m : ℕ}
  (hc : roomCost H.levels W) (hb : Bank W H.levels)
local notation "L" => H.S.block m
local notation "K" => W.K (H.levels.clock.J (m+1))
include hc hb
lemma worthCore (h : Triangle H W m x y) (v : F.Coeff) :
    μ (F.core (y v)) ≤ ((L).val:ℝ)^(d-3) * μ (F.core (x v)) := by
  obtain ⟨T,hT,hQ,herr⟩ := h.leads
  by_cases hd : 4 ≤ d
  swap
  · rw [beforeFirst F hG (y v) (by omega),beforeFirst F hG (x v) (by omega)]
    simp [Frame.coeffSize]
  let w := μ (F.core (x v))
  let a : ℝ := ((L).val:ℝ)
  have hk : 1 ≤ K := W.prices _
  have ht : F.core (T.leads L (x v)) = T.leads L (F.core (x v)) := by
    change F.core (T.map (vowel F L _)) = T.map _
    rw [← T.core_comm, core_vowel]
    rfl
  have hp : μ (F.core (T.leads L (x v))) ≤ K*(a^(d-4)*w) :=
    ht ▸ ((hQ (vowel F L (F.core (x v)))).1).trans (mul_le_mul_of_nonneg_left (upToFirst F hG ..) (zero_le_one.trans hk))
  have he : d-3=d-4+1 := by omega
  calc
    _ ≤ μ (F.core (T.leads L (x v))) + μ (F.core (y v - T.leads L (x v))) := by rw [map_sub]; exact size_triangle F _ _
    _ ≤ K*(a^(d-4)*w) + barunit L*w := add_le_add hp ((size_core F _).trans (herr v))
    _ ≤ _ := by rw [he]; exact oneBlockCost hc hb _ (size_nonneg ..)

section all
omit hc hb hG
variable {C : Family G} {r D} {k j N p : ℕ}
def coreQuota (C : Family G) (d k N p : ℕ) (x : C.label d) : ℝ :=
  (C.labels.level d).coeffSize ((C.labels.level d).core
    (((C.factory d N p).entries k ((C.factory d N p).terminal.symm x)).x))
lemma coreQuota_le (x : C.label d) : coreQuota C d k N p x ≤ quota C d k N p x := size_core ..

include hG
lemma corePrice (T : TableTickets C W r D)
    (x : C.label d) (hr : C.ref d ≤ k) (hk : k ≤ j) (hn : j ≤ N) :
    coreQuota C d k N p x ≤ (C.S.a k / C.S.a j)^(d-3) * coreQuota C d j N p x := by
  induction hk using Nat.decreasingInduction with
  | self => rw [div_self (C.S.a_pos j).ne', one_pow, one_mul]
  | of_succ i hi ih =>
    specialize ih (hr.trans (Nat.le_succ i))
    calc
      _ ≤ ((C.S.block i).val:ℝ)^(d-3) * coreQuota C d (i+1) N p x := worthCore hG
          T.system.costs.cost T.system.costs.back (T.columns d N p ((hr.trans hi.le).trans hn) i hr (hi.trans_le hn)) _
      _ ≤ ((C.S.block i).val:ℝ)^(d-3) * _ := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [show C.S.a i = ((C.S.block i).val:ℝ)*C.S.a (i+1) from ?_,mul_div_assoc,mul_pow, ←mul_assoc]
                  rw [Schedule.a_step, mul_div_cancel₀ _ (by positivity)]

omit hG
variable (T : TableTickets C W r D) (h : C.Makes)
local notation "F!" => C.labels.level d
include T h
lemma reference (x : C.label d) (hr : C.ref d ≤ k) (hk : k ≤ N) :
    ‖x‖ ≤ (C.S.a (C.ref d) / C.S.a k)^d * quota C d k N p x := by
  have h₁ := passPrice (p:=p) T x le_rfl hr hk
  unfold quota at h₁
  rw [C.normalized h (hr.trans hk) x] at h₁
  exact (Size.norm_le ..).trans h₁

lemma referenceCore (hG' : G.Simple) (x : C.label d) (hr : C.ref d ≤ k) (hk : k ≤ N) :
    ‖(F!).core x‖ ≤ (C.S.a (C.ref d) / C.S.a k)^(d-3) * coreQuota C d k N p x := by
  have h₁ := corePrice (p:=p) hG' T x le_rfl hr hk
  unfold coreQuota at h₁
  rw [C.normalized h (hr.trans hk) x] at h₁
  exact (Size.norm_le ..).trans h₁
end all
end YM.SharpGram
