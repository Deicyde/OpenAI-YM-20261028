import YM.Next.UV_STRESS.Ramp

/-!
# Lanes evaluated on joint old/new arrays

Include true moments against a varying probe introduced at level k. Distinct
from `Overlay.Lane.from_` on only old moments. Keep scale factors in this
section before introducing new markers. All statements at same N through
chosen path. Test RP or other expectations only against integrable products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Measure Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Census ι} {N p ℓ k m : ℕ}

section back
lemma final_mul {α} [MeasurableSpace α] (μ : Measure α) (D E : α → ℂ) (hd : Envelope D) (he : Integrable E μ) :
    Integrable (fun x => D x*E x) μ := by
  obtain ⟨x,hx⟩ := hd.cost
  exact he.bdd_smul x hd.meas.aestronglyMeasurable (Eventually.of_forall hx)

lemma reads_joint (β : ℝ) (F : Config G (C.side m p)→ℂ) (h : Envelope F)
    (K : Config G (C.side (m+1) p) → ℂ) (hp : Integrable K (prior G (C.side (m+1) p))) :
    let r:=operation C p m
    (∫ V,F V * r.push β K V ∂prior G (C.side m p)) =
      ∫ U, back r β F U * K U ∂prior G (C.side (m+1) p) := by
  intro r
  let f (U) (V) := F V*(r.density β U V • K U)
  have hh V : F V * r.push β K V=∫ U, f U V ∂prior G _ := (integral_const_mul ..).symm
  have hz U : back r β F U * K U = ∫ V, f U V ∂prior G _ := by
    unfold back; rw [← integral_mul_const]; apply integral_congr_ae; filter_upwards with V
    simp only [f,Complex.real_smul]; ring
  simp_rw [hh,hz]
  have he := C.path.levels.transition_mass m p β
  rw [integral_integral_swap]
  let μ := prior G (C.side (m+1) p); let ν := prior G (C.side m p)
  change Integrable ((uncurry f) ∘ Prod.swap) _
  apply Integrable.swap
  apply final_mul (μ.prod ν) (fun x => F x.2) _
  · exact ⟨h.meas.comp measurable_snd,_,fun x => h.cost.choose_spec _⟩
  exact StepData.push_integrand he _ hp

variable (L : Overlay.Lane C.path R N p) (h : L.Works k)
include h
-- Compare b extensions
lemma basis_jump (P : C.Makes) (F : Config G (C.side k p)→ℂ) (he : Envelope F)
    {m} (hm : k≤m) (ht : m ≤ N) (s : R.Mode) :
    (∫ V, stack C p N k m F hm V * L.signal m s V ∂prior G _) = Ride.bump (C.S.a m) s L.load *
      (partition G (C.side N p) (C.beta N p):ℂ) * moment (C.beta N p) (fun U => stack C p N k N F h.admits U *
        Ride.Product L.uses s U) := by
  induction ht using Nat.decreasingInduction with
  | self =>
    have hh : Integrable (fun U => stack C p N k N F hm U * Ride.Product L.uses s U) (law G _ (C.beta N p)) :=
      final_mul _ _ _ (stack_envelope C _ _ _ _ _ hm he) (h.reads s)
    rw [moment_formula _ _ hh,mul_assoc,mul_inv_cancel_left₀ (by exact_mod_cast (partition_pos (G:=G) (n:=C.side N p) (C.beta N p)).ne'),← integral_const_mul]; apply integral_congr_ae; filter_upwards with x
    rw [h.first s]
    change _*_ = Ride.bump (C.path.S.a N) s L.load *(↑(bare (C.path.β N p N) x) * _)
    ring
  | of_succ i hi ih =>
    let U := stack C p N k i F hm
    let j := Ride.bump (R:=R) (C.S.block i).val s L.load
    let D := L.signal (i+1) s
    have hx (x) : U x * L.signal i s x=j*(U x*(operation C p i).push (C.path.β N p (i+1)) D x) := by
      rw [h.step i hm hi s]; change _*(j* _) = _; ring
    have hr := h.meaningful (i+1) (hm.trans (Nat.le_succ _)) hi
    obtain ⟨hs,w,u,c,d,b,hv⟩ := hr
    have H : Integrable D (prior G _) := ((L.sites _).material hs hv (P.wilson.represents N p (i+1) hi).good
      (beta_positive P.wilson hi).le s).1
    specialize ih (hm.trans (Nat.le_succ _)); simp_rw [stack_step C _ _ _ _ F hm] at ih
    change (∫ V, U V * L.signal i s V ∂prior G _) = _
    simp_rw [hx]
    rw [integral_const_mul, reads_joint C _ _ (stack_envelope C _ _ _ _ _ hm he) D H]
    unfold D; rw [ih,bump_steps C i]; unfold j; ring
end back
end YM.Next.UVStress
