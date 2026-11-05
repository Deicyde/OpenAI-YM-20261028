import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Gauge2
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Speed
import YM.Next.EXTRACTION.Mixture

/-!
# Local change of the affine matrix, angular gauges

Torus/sector-uniform. $Dmat$ retains every old $a$ and frame/min tag
in its comparison applications: reanchor orientations, don't minimize
an unrelated objective. Compact comparison only on fixed path widths.
Weights $C_L R^j$ here safe at post-L; curved Gram prices later from
these, not estimates on the outputs on tests after continuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Turn
open Matrix Work.F03 Progress.StationaryScenes Push.AbsoluteSums Tree Next.Fluctuations
open Win  
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def plane (T : Tube G S) (R : ℕ) (i : Pos S) (x : Directions G f) := i.2.elim
    (fun p => level T R p x) (fun p => zLin S (form x) 0 p)

def insideD (m : StepData c f) (p : Pos m) (e : Bond f) := separation (center m p.2) (home m e)

lemma level_range (T : Tube G S) (R : ℕ) (p : Twin f) (x y : Directions G f)
    (hx : ∀ i : Bond f,separation (S.ratio.parent p.1.1) (home S i) ≤ stencilD S.patch R → x i=y i) :
    level T R p x = level T R p y := by
  unfold level; split
  next h =>
    apply tsum_congr
    intro l; change bandTerm T _ _ _ _=bandTerm T _ _ _ _; unfold bandTerm; split
    next hb =>
      refine congr_arg _ (curl_range S _ _ _ fun i h => hx _ ?_)
      let s := (T.up.row p.1.2 l).2
      apply (separation_triangle _ (S.ratio.parent (slotFace s p.1.1).1) _).trans
      refine le_trans (Nat.add_le_add (trunc_range (S:=S) _ _) h) ?_
      change s.walk.length + 4 ≤ R at hb
      unfold stencilD; omega
    next => rfl
  next h =>
    refine congr_arg _ (curl_range S _ _ _ fun i h => hx _ ?_); unfold stencilD; omega

lemma plane_range (T : Tube G S) (R : ℕ) (p : Pos S) (x y : Directions G f) (hb : S.patch.Branches S.kernel G)
    (he : ∀ i : Bond f, insideD S p i≤stencilD S.patch R → x i=y i) : plane T R p x = plane T R p y := by
  rcases p with ⟨s,i|i⟩
  · exact level_range T _ _ _ _ he
  apply z_range hb; intro i h; apply he
  apply Nat.le_trans h (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))

lemma plane_add (T : Tube G S) (R : ℕ) (p : Pos S) (x y : Directions G f) {P : Teller G} (hp : P.Funds S T) :
    plane T R p (x+y)=plane T R p x+plane T R p y := by
  rcases p with ⟨s,i|i⟩
  · exact level_add hp ..
  unfold plane; simp only [Sum.elim_inr,noise_linear]
  rw [show form (x+y)=form x+form y from rfl]; simp only [Pi.add_apply, smul_add,Finset.sum_add_distrib]

/-- Physical sup. -/
lemma plane_uniform (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) :
    ∃ W : ℝ, 0<W ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
      ∀ (R : ℕ) (i : Pos S) (x : Directions G f) (v : ℝ), 0≤v →
        (∀ e : Bond f, insideD S i e ≤ stencilD S.patch R → ‖x e‖ ≤ v) →
        ‖plane T R i x‖ ≤ W*v := by
  obtain ⟨A,r,hA,-,ha⟩ := z_chart_cost D P.bind G hb
  let C := P.top.paths; let s := Real.sqrt P.top.clip.direct
  have hs : 0 ≤ s := Real.sqrt_nonneg _; have hc : 0<C := P.top.paths_pos
  refine ⟨4*(s+C)+A,by positivity,?_⟩
  intro c f S T hD hT R i x v hv h
  let y (j : Bond f) := if insideD S i j ≤ stencilD S.patch R then x j else 0
  have hi : plane T R i x=plane T R i y := plane_range T R i _ _ (hT.knobs.symm ▸ hT.kernel) fun i he => by
    unfold y; rw [if_pos he]
  have hh j : ‖y j‖ ≤ v := by
    unfold y; split
    next he => exact h j he
    next => rw [norm_zero]; exact hv
  rw [hi]
  obtain ⟨α,Λ,hx,hV⟩ := hT.feeds
  rcases i with ⟨a,i|i⟩
  · change ‖level T R i y‖ ≤ _; unfold level; split
    next ht =>
      let P' l := |(T.up.row i.1.2 l).1| * Real.exp (P.top.width*(T.up.row i.1.2 l).2.length)
      have hf l : ‖bandTerm T R i.1 l y‖ ≤ P' l*(4*v) := by
        unfold bandTerm; split
        next h =>
          rw [norm_smul]; apply mul_le_mul _ (curl_cost _ _ _ hh) (by positivity) (by unfold P'; positivity)
          exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg P.top.width_pos.le (by positivity)))
        next h => rw [norm_zero]; unfold P'; positivity
      have he : SumBudget P' C := hx.rows i.1.2
      have hz := (he.2.1.mul_right (4*v)).of_nonneg_of_le (fun j => norm_nonneg _) hf
      calc
        _ ≤ ∑' l, P' l*(4*v) := (norm_tsum_le_tsum_norm hz).trans (hz.tsum_le_tsum hf (he.2.1.mul_right (4*v)))
        _ ≤ C*(4*v) := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right he.2.2 (by positivity)
        _ ≤ _ := by nlinarith
    next ht =>
      rw [hT.high]
      change ‖s • curl i.1 y‖ ≤ _; rw [norm_smul,Real.norm_of_nonneg hs]
      exact (mul_le_mul_of_nonneg_left (curl_cost _ _ _ hh) hs).trans (by nlinarith)
  have he : ‖(form y, (0:fieldDir G c 1))‖≤v := max_le
    ((pi_norm_le_iff_of_nonneg hv).mpr (fun j => hh _)) (by rw [norm_zero]; exact hv)
  exact ((ha c f S hD hT.knobs (Classical.ofNonempty:S.Choices) i (form y,0)).1.trans (mul_le_mul_of_nonneg_left he hA.le)).trans
    (by nlinarith)

section patch
variable (S : StepData c f)
lemma directed_climb (s : Signed) (x : Site n) (p : Bond n) :
    separation (s.act x) (edgeP s p).1 ≤ separation x p.1 + 1 := by
  apply le_trans (separation_triangle _ (s.act p.1) _)
  rw [separation_signed]
  have he : s.act p.1∈pinPos (edgeP s p) := by
    rw [pin_map]; exact Finset.mem_image_of_mem _ (by simp [pinPos])
  rcases Finset.mem_insert.mp he with he|he
  · exact Nat.add_le_add_left (show separation (s.act p.1) (edgeP s p).1 ≤ 1 by rw [he]; simp) _
  apply Nat.add_le_add_left; rw [Finset.mem_singleton.mp he, separation_comm]; exact Work.E03.sep_step _ _

lemma directed_cost (V : Config G n) (s : Signed) (e : Bond n) : G.chord (pull s 0 V e) = G.chord (V (edgeP s e)) := by
  rw [step_transport]; split <;> simp

-- bound transport along specified stencil ONLY locally
lemma near_cost (V : Config G n) (x : Site n) (w : Walk) {δ : ℝ} (ht : 0 ≤ δ)
    (h : ∀ i : Bond n, separation x i.1 ≤ w.length → G.chord (V i) ≤ δ) : G.chord (travel V x w) ≤ w.length*δ := by
  let U (e : Bond n) : G.El := if separation x e.1 ≤ w.length then V e else 1
  have he : AgreeNear id x w.length V U := fun i hi => (if_pos hi).symm
  rw [travel_near id (fun y i => Work.E03.sep_step y i) V U x w w.length le_rfl he]; refine travel_chord U w x δ ?_
  intro i; unfold U; split
  next hi => exact h i hi
  next hi => rw [G.chord_one]; exact ht

lemma aiming_cost (x : Site n) (R : ℕ) {δ : ℝ} (ht : 0 ≤ δ) (V : Config G n)
    (h : ∀ i : Bond n, separation x i.1 ≤ 4*R → G.chord (V i) ≤ δ) :
    ∀ y : Site n, separation x y ≤ R → G.chord (aiming V x y) ≤ (4*R:ℕ)*δ := by
  intro y hy
  have hg : (corner x y).length ≤ 4*R := (path_length x y).trans (by omega)
  apply (near_cost V x (corner x y) ht (fun i hi => h i (hi.trans hg))).trans
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hg) ht

private lemma maps_price (s : Signed) (U : Config G n) (y : Bond n) (v : Directions G n) (δ : ℝ) (B : ℝ)
    (hd : G.chord (U (edgeP s y)) ≤ δ) (hb : ‖v (edgeP s y)‖ ≤ B) :
    ‖maps s U v y - maps s 1 v y‖ ≤ 2 * G.colorScale * δ * B := by
  have hx := G.colorScale_pos
  have hm := (G.chord_nonneg _).trans hd; have hf := (norm_nonneg _).trans hb
  rw [maps_apply,maps_apply]; split
  next h =>
    simp only [Pi.one_apply, inv_one, G.adjoint_one, neg_sub_neg, norm_sub_rev (v (edgeP s y))]
    apply (adjoint_norm_sub _ _).trans; rw [G.chord_inv]; gcongr
  next h => rw [sub_self,norm_zero]; positivity

/-- At a particular orientation p and v sup-stencil, use ANY fixed-frame
shrink (all inputs in this gauge). -/
lemma untwist (p : Pos S) (R : ℕ) (x : Directions G f) (C δ : ℝ) (hd : 0 ≤ δ) (_hx : 0 ≤ C)
    (V : Config G c) (h : ∀ i : Bond c, separation (base S p) i.1 ≤ 4*R+1 → G.chord (V i) ≤ δ)
    (hc : ∀ i : Bond f,separation (base S p) (home S i) ≤ R+1 → ‖x i‖ ≤ C) :
    ∀ i : Bond f, insideD S p i ≤ R → ‖untwine S p V x i - untwine S p 1 x i‖ ≤
      2 * G.colorScale*((4*R:ℕ)+1:ℝ)*δ*C := by
  intro i hi
  let s := p.1; let U := replica S.ratio V
  have hw : separation (base S p) (home S (edgeP s i)) ≤ R+1 :=
    (along_home s (center S p.2) S i).trans (Nat.add_le_add_right hi _)
  have he : maps s U x i = _ := maps_apply s U ..
  let a := maps s U x i; let b := maps s (1:Config G f) x i
  have hy := aiming_cost (center S p.2) R hd (pull s 0 V) (by
    intro j hj; rw [directed_cost]; apply h
    exact (directed_climb s (center S p.2) j).trans (by omega)) (home S i) hi
  let g := aiming (pull s 0 V) (center S p.2) (home S i)
  have hg : ∀ (p : Walk) (x : Site c), travel (pull s 0 (1:Config G c)) x p = 1 := by
    intro p x; rw [travel_pull, ← Precision.link_one (n:=c)]; exact Push.stroll_zero ..
  have hh : untwine S p 1 x i=b := by
    change G.adjoint (aiming (pull s 0 _) (center S p.2) (home S i)) _ = b
    dsimp only [aiming]; rw [hg]; simp only [G.adjoint_one, replica_one]; rfl
  have hU : G.chord (U (edgeP s i)) ≤ δ := by
    unfold U replica; split
    next h => rw [G.chord_one]; exact hd
    next _ => exact h _ (hw.trans (by omega))
  have hA : ‖a‖ ≤ C := by unfold a; rw [maps_cost]; exact hc _ hw
  rw [hh]
  apply (norm_sub_le_norm_sub_add_norm_sub (G.adjoint g a) a b).trans
  calc
    _ ≤ 2 * G.colorScale * G.chord g * ‖a‖ + 2*G.colorScale*δ*C :=
        add_le_add (adjoint_norm_sub g a) (maps_price s U i x δ C hU (hc _ hw))
    _ ≤ 2*G.colorScale*((4*R:ℕ)*δ)*C+2*G.colorScale*δ*C := by have h := G.colorScale_pos; gcongr
    _ = _ := by ring
end patch

/-- Local perturbation of D, uniformly for ANY v satisfying the stencil
bound in THAT gauge. Post-L. Radius `R` permitted up to the actual
truncation budget; any tests that need shorter range can take smaller R
(and use e.g. equality at direct p/Q jets, no dependence on R in those).
Cost polynomial in stencil. -/
theorem perturb (P : Teller G) (D : Patch) (hb : D.Branches P.bind G) :
    ∃ B : ℝ, 0<B ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
      ∀ (R : ℕ) (p : Pos S) (x : Directions G f) (C δ : ℝ), 0≤C → 0≤δ →
        let D := stencilD S.patch R
        (∀ i : Bond f,separation (base S p) (home S i) ≤ D+1 → ‖x i‖ ≤ C) →
        ∀ V : Config G c, (∀ i : Bond c, separation (base S p) i.1 ≤ 4*D+1 → G.chord (V i) ≤ δ) →
        ‖derivative T R p V x-derivative T R p 1 x‖ ≤ B*((4*D:ℕ)+1:ℝ)*δ*C := by
  obtain ⟨B,hB,H⟩ := plane_uniform P D hb
  refine ⟨B*(2*G.colorScale),mul_pos hB (mul_pos two_pos G.colorScale_pos),?_⟩
  intro c f S T hD hT R p x C δ hC hδ D hx V hv
  let a := untwine S p V x; let b := untwine S p 1 x
  have ht : plane T R p a - plane T R p b=plane T R p (a-b) := by
    have hh := plane_add T R p (a-b) b hT; rw [sub_add_cancel] at hh; rw [hh,add_sub_cancel_right]
  change ‖plane T R p a-plane T R p b‖ ≤ _; rw [ht]
  have hh := untwist S p D x C δ hδ hC V hv hx
  apply le_trans (H c f S T hD hT R p (a-b) (2*G.colorScale*((4*D:ℕ)+1:ℝ)*δ*C) (by have h := G.colorScale_pos; positivity) hh)
  exact le_of_eq (by ring)
end YM.AnalyticNext.ConnectedActivity.Aff
