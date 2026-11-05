import YM.Cells.Certificate



/-!
# Bracket moving support before applying centered bounds

Literal translates, may not be on the same blocking offsets. Geometry of
interpolants checked at larger side in use. Handles zeros, both seam types.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open MeasureTheory Measure Function Set Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (T : Tiling n) (β : ℝ)

private theorem max_end (g : ℕ → ℝ) (m : ℕ) (hn : ∀ i, i ≤ m → 0 ≤ g i) (A : ℝ)
    (H : ∀ i, i+2 ≤ m → g (i+1)^2 ≤ g i*g (i+2)) (h : g 0 ≤ A) (he : g m≤A) : ∀ i ≤ m, g i ≤ A := by
  -- strict increase propagates
  have hv i (hp : i+1 ≤ m) (hr : g i < g (i+1)) : g (i+1) ≤ A := by
    have he_idx (p : ℕ) (hr' : g p<g (p+1)) (hs : p+2≤m) : g (p+1)<g (p+2) := by
      have hl := H p hs
      have ha := hn p (by omega)
      have hh := hn (p+2) hs
      by_contra! hv
      apply (not_le.mpr ?_ hl)
      calc _ ≤ g p * g (p+1) := by gcongr
           _ < _ := by nlinarith
    have ht (q : ℕ) (hq : i≤q) (hz : q+1≤m) : g q<g (q+1) ∧ g (i+1) ≤ g (q+1) := by
      induction q, hq using Nat.le_induction with
      | base => exact ⟨hr,le_rfl⟩
      | succ n hn ih => exact ⟨he_idx _ (ih (by omega)).1 hz,(ih (by omega)).2.trans (he_idx _ (ih (by omega)).1 hz).le⟩
    have hs : g (i+1) ≤ g ((m-1)+1) := (ht _ (by omega) (by omega)).2
    rw [show m-1+1=m by omega] at hs; exact hs.trans he
  intro i hi; induction i with
  | zero => exact h
  | succ i ih => exact le_or_gt (g (i+1)) (g i) |>.elim (fun h => h.trans (ih (by omega))) (fun h => hv i hi h)

private theorem safety (s : Signed) (r : Axis) (v : T.Cell) (h : s=T.omega v) :
    s.act (step r : Site n) = if s.flip r then - step r else step r := by
  subst s
  ext1 i
  rw [show (T.omega v).act (step r : Site n) i = _ from Signed.act_at (T.omega v) _ i]
  split_ifs with H I <;> by_cases he:i=r <;> simp_all

private lemma read_move (k : T.Cell) (b : Axis) (u : Config G n) (F : Config G n → ℂ) :
    T.copy k F (translate (step b) u)=
      if (T.omega k).flip b then T.copy k (F ∘ translate (-step b)) u else T.copy k (F ∘ translate (step b)) u := by
  have he := safety T _ b k rfl
  classical
  simp_rw [copy]
  have hp (t : Site n) (h : (T.omega k).act t = step b) : translate t (pull (T.omega k) (T.translateBy k) u)=
      pull (T.omega k) (T.translateBy k) (translate (step b) u) := by
    rw [← pull_one, ← pull_one,pull_pull,pull_pull]
    simp [affine,h,add_comm]
  by_cases hv : T.hand k <;> cases h:(T.omega k).flip b <;> simp [hv] <;> simp_all

/-- It suffices that F & both translates are allowed interior words. -/
theorem trip (L : Seam G n β) {F : Config G n → ℂ} (b : Axis) (Hp : Interior (T.chamber 0) F)
    (h : Interior (T.chamber 0) (F ∘ translate (-step b))) (he : Interior (T.chamber 0) (F ∘ translate (step b))) :
    T.rootTest β F ^ 2 ≤ T.rootTest β (F ∘ translate (-step b))*T.rootTest β (F ∘ translate (step b)) := by
  classical
  let W (v : T.Cell) := if (T.omega v).flip b then F ∘ translate (-step b) else F ∘ translate (step b)
  have hm := T.manyIntegral β (fun _ => F) fun _ => Hp
  have ht : T.rootTest β F ^ Fintype.card T.Cell ≤ ∏ i : T.Cell, T.rootTest β (W i) := by
    rw [T.powering,rootPower, ← moment_pull β 1 (step b) _ hm]
    have hhx (U : Config G n) : T.fullAt (fun _ => F) (pull 1 (step b) U) = ∏ i, T.copy i (W i) U := by
      rw [pull_one,fullAt]
      apply Finset.prod_congr rfl
      intro i _; rw [read_move];split <;> simp [W, *]
    simp only [Function.comp_def, hhx]; exact L.inequality T W fun i => by unfold W; split; exacts [h,he]
  let P := Equiv.ofBijective (T.mate 0 b) (Function.Involutive.bijective (T.mate_invol 0 b))
  have hv (i): (T.omega (P i)).flip b = !(T.omega i).flip b := T.flip_here 0 b i
  let w (i) := T.rootTest β (W i)
  let ξ := T.rootTest β (F ∘ translate (-step b))*T.rootTest β (F ∘ translate (step b))
  have hf : (∏ i:T.Cell, w i)^2=ξ^(Fintype.card T.Cell) := calc
    _ = (∏ i:T.Cell,w i) * ∏ j:T.Cell,w (P j) := by rw [pow_two, Equiv.prod_comp]
    _ = ∏ i:T.Cell, ξ := by
      rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _
      cases H:(T.omega i).flip b <;> simp [W,hv,H,ξ,w,mul_comm]
    _ = _ := by simp
  haveI : Nonempty T.Cell := ⟨0⟩
  apply le_of_pow_le_pow_left₀ (show 0<Fintype.card T.Cell from Fintype.card_pos).ne' (mul_nonneg (T.root_nonneg β _) (T.root_nonneg β _))
  rw [← show (∏ i:T.Cell,w i)^2=_ from hf, ← pow_mul,pow_mul']
  apply pow_le_pow_left₀ (pow_nonneg (T.root_nonneg ..) _) ht

/-- If all integral offsets fit, z is bounded by endpoints. -/
theorem pathway (L : Seam G n β) (F : ℕ → Config G n → ℂ) (s : ℕ) (b : Axis)
    (H : ∀ u ≤ s, Interior (T.chamber 0) (F u))
    (h : ∀ u, u+1≤s → F (u+1)= F u ∘ translate (step b))
    (A : ℝ) (hf : T.rootTest β (F 0) ≤ A) (hh : T.rootTest β (F s)≤A) : ∀ u ≤ s, T.rootTest β (F u) ≤ A := by
  refine max_end (fun u => T.rootTest β (F u)) s (fun u _ => T.root_nonneg ..) A ?_ hf hh
  intro i hi; set f := F (i+1); change T.rootTest β (F (i+1))^2 ≤ _
  have hv : F (i+1) ∘ translate (-step b)=F i := by
    rw [h i (by omega)]
    funext U
    have he : translate (step b) (translate (-step b) U)=U := by ext1 q; simp [translate]
    exact congr_arg _ he
  have hw := h (i+1) hi
  rw [← hv,hw]; exact T.trip β L b (H _ (by omega)) (hv.symm ▸ H i (by omega)) (hw ▸ H (i+2) hi)
end YM.Cells.Tiling
